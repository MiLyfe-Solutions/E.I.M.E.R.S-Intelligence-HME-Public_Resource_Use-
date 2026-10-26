import V185TrunkScan23Chunk0899

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5326629 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 3, 1, 4]
def baseStart_5326629 : Nat := 118140960795 + 5326629 * 2 ^ 59
def prefixEnd_5326629 : Nat := 4983230072969 + 3 ^ 40 * 5326629 * 2
def baseEnd_5326629 : Nat := 2735120945177945273240785

theorem tailTrace_5326629 : CollatzResearch.WordTrace tailWord_5326629 prefixEnd_5326629 2735120945177945273240785 := by
  unfold tailWord_5326629
  simp only [CollatzResearch.WordTrace]
  refine ⟨194278120219540323652134941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129518746813026882434756627 194278120219540323652134941)
  ·
    refine ⟨72854295082327621369550603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194278120219540323652134941 72854295082327621369550603)
    ·
      refine ⟨109281442623491432054325905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72854295082327621369550603 109281442623491432054325905)
      ·
        refine ⟨81961081967618574040744429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109281442623491432054325905 81961081967618574040744429)
        ·
          refine ⟨30735405737856965265279161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81961081967618574040744429 30735405737856965265279161)
          ·
            refine ⟨23051554303392723948959371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30735405737856965265279161 23051554303392723948959371)
            ·
              refine ⟨34577331455089085923439057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23051554303392723948959371 34577331455089085923439057)
              ·
                refine ⟨25932998591316814442579293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34577331455089085923439057 25932998591316814442579293)
                ·
                  refine ⟨9724874471743805415967235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25932998591316814442579293 9724874471743805415967235)
                  ·
                    refine ⟨14587311707615708123950853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9724874471743805415967235 14587311707615708123950853)
                    ·
                      refine ⟨2735120945177945273240785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14587311707615708123950853 2735120945177945273240785)
                      ·
                        rfl

theorem cell23_5326629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_5326629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326629 prefixEnd_5326629 := by exact prefixLift 5326629
  have htrace : WordTrace (prefixWord ++ tailWord_5326629) baseStart_5326629 baseEnd_5326629 := by
    simpa [prefixWord, tailWord_5326629, baseEnd_5326629] using wordTrace_append hprefix tailTrace_5326629
  have hstable : (prefixWord ++ tailWord_5326629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326629).length < 2 ^ (prefixWord ++ tailWord_5326629).sum := by decide
  have hdescent : baseEnd_5326629 < baseStart_5326629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326652 : List Nat := [2, 2, 2, 2, 1, 1, 2, 11]
def baseStart_5326652 : Nat := 118140960795 + 5326652 * 2 ^ 59
def prefixEnd_5326652 : Nat := 4983230072969 + 3 ^ 40 * 5326652 * 2
def baseEnd_5326652 : Nat := 101301213156777729009377

theorem tailTrace_5326652 : CollatzResearch.WordTrace tailWord_5326652 prefixEnd_5326652 101301213156777729009377 := by
  unfold tailWord_5326652
  simp only [CollatzResearch.WordTrace]
  refine ⟨97139479549228499290111105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129519306065637999053481473 97139479549228499290111105)
  ·
    refine ⟨72854609661921374467583329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97139479549228499290111105 72854609661921374467583329)
    ·
      refine ⟨54640957246441030850687497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72854609661921374467583329 54640957246441030850687497)
      ·
        refine ⟨40980717934830773138015623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54640957246441030850687497 40980717934830773138015623)
        ·
          refine ⟨61471076902246159707023435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40980717934830773138015623 61471076902246159707023435)
          ·
            refine ⟨92206615353369239560535153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61471076902246159707023435 92206615353369239560535153)
            ·
              refine ⟨69154961515026929670401365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92206615353369239560535153 69154961515026929670401365)
              ·
                refine ⟨101301213156777729009377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 69154961515026929670401365 101301213156777729009377)
                ·
                  rfl

theorem cell23_5326652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 11].length) (baseStart_5326652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326652 prefixEnd_5326652 := by exact prefixLift 5326652
  have htrace : WordTrace (prefixWord ++ tailWord_5326652) baseStart_5326652 baseEnd_5326652 := by
    simpa [prefixWord, tailWord_5326652, baseEnd_5326652] using wordTrace_append hprefix tailTrace_5326652
  have hstable : (prefixWord ++ tailWord_5326652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326652).length < 2 ^ (prefixWord ++ tailWord_5326652).sum := by decide
  have hdescent : baseEnd_5326652 < baseStart_5326652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326659 : List Nat := [1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 4]
def baseStart_5326659 : Nat := 118140960795 + 5326659 * 2 ^ 59
def prefixEnd_5326659 : Nat := 4983230072969 + 3 ^ 40 * 5326659 * 2
def baseEnd_5326659 : Nat := 2735136349597580155865647

theorem tailTrace_5326659 : CollatzResearch.WordTrace tailWord_5326659 prefixEnd_5326659 2735136349597580155865647 := by
  unfold tailWord_5326659
  simp only [CollatzResearch.WordTrace]
  refine ⟨194279214409431638775727031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129519476272954425850484687 194279214409431638775727031)
  ·
    refine ⟨291418821614147458163590547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194279214409431638775727031 291418821614147458163590547)
    ·
      refine ⟨437128232421221187245385821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291418821614147458163590547 437128232421221187245385821)
      ·
        refine ⟨163923087157957945217019683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 437128232421221187245385821 163923087157957945217019683)
        ·
          refine ⟨245884630736936917825529525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163923087157957945217019683 245884630736936917825529525)
          ·
            refine ⟨23051684131587836046143393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 245884630736936917825529525 23051684131587836046143393)
            ·
              refine ⟨17288763098690877034607545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23051684131587836046143393 17288763098690877034607545)
              ·
                refine ⟨12966572324018157775955659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17288763098690877034607545 12966572324018157775955659)
                ·
                  refine ⟨19449858486027236663933489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12966572324018157775955659 19449858486027236663933489)
                  ·
                    refine ⟨14587393864520427497950117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19449858486027236663933489 14587393864520427497950117)
                    ·
                      refine ⟨2735136349597580155865647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14587393864520427497950117 2735136349597580155865647)
                      ·
                        rfl

theorem cell23_5326659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_5326659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326659 prefixEnd_5326659 := by exact prefixLift 5326659
  have htrace : WordTrace (prefixWord ++ tailWord_5326659) baseStart_5326659 baseEnd_5326659 := by
    simpa [prefixWord, tailWord_5326659, baseEnd_5326659] using wordTrace_append hprefix tailTrace_5326659
  have hstable : (prefixWord ++ tailWord_5326659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326659).length < 2 ^ (prefixWord ++ tailWord_5326659).sum := by decide
  have hdescent : baseEnd_5326659 < baseStart_5326659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326666 : List Nat := [3, 1, 2, 1, 1, 1, 5, 3, 1, 2, 3]
def baseStart_5326666 : Nat := 118140960795 + 5326666 * 2 ^ 59
def prefixEnd_5326666 : Nat := 4983230072969 + 3 ^ 40 * 5326666 * 2
def baseEnd_5326666 : Nat := 2735139943962161628478115

theorem tailTrace_5326666 : CollatzResearch.WordTrace tailWord_5326666 prefixEnd_5326666 2735139943962161628478115 := by
  unfold tailWord_5326666
  simp only [CollatzResearch.WordTrace]
  refine ⟨48569867430101569742807963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129519646480270852647487901 48569867430101569742807963)
  ·
    refine ⟨72854801145152354614211945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48569867430101569742807963 72854801145152354614211945)
    ·
      refine ⟨54641100858864265960658959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72854801145152354614211945 54641100858864265960658959)
      ·
        refine ⟨81961651288296398940988439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54641100858864265960658959 81961651288296398940988439)
        ·
          refine ⟨122942476932444598411482659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81961651288296398940988439 122942476932444598411482659)
          ·
            refine ⟨184413715398666897617223989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122942476932444598411482659 184413715398666897617223989)
            ·
              refine ⟨17288785818625021651614749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184413715398666897617223989 17288785818625021651614749)
              ·
                refine ⟨6483294681984383119355531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17288785818625021651614749 6483294681984383119355531)
                ·
                  refine ⟨9724942022976574679033297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6483294681984383119355531 9724942022976574679033297)
                  ·
                    refine ⟨7293706517232431009274973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9724942022976574679033297 7293706517232431009274973)
                    ·
                      refine ⟨2735139943962161628478115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7293706517232431009274973 2735139943962161628478115)
                      ·
                        rfl

theorem cell23_5326666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_5326666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326666 prefixEnd_5326666 := by exact prefixLift 5326666
  have htrace : WordTrace (prefixWord ++ tailWord_5326666) baseStart_5326666 baseEnd_5326666 := by
    simpa [prefixWord, tailWord_5326666, baseEnd_5326666] using wordTrace_append hprefix tailTrace_5326666
  have hstable : (prefixWord ++ tailWord_5326666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326666).length < 2 ^ (prefixWord ++ tailWord_5326666).sum := by decide
  have hdescent : baseEnd_5326666 < baseStart_5326666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326672 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 6]
def baseStart_5326672 : Nat := 118140960795 + 5326672 * 2 ^ 59
def prefixEnd_5326672 : Nat := 4983230072969 + 3 ^ 40 * 5326672 * 2
def baseEnd_5326672 : Nat := 2735143024846088605003087

theorem tailTrace_5326672 : CollatzResearch.WordTrace tailWord_5326672 prefixEnd_5326672 2735143024846088605003087 := by
  unfold tailWord_5326672
  simp only [CollatzResearch.WordTrace]
  refine ⟨97139844279192270997975135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129519792372256361330633513 97139844279192270997975135)
  ·
    refine ⟨145709766418788406496962703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97139844279192270997975135 145709766418788406496962703)
    ·
      refine ⟨218564649628182609745444055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145709766418788406496962703 218564649628182609745444055)
      ·
        refine ⟨327846974442273914618166083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218564649628182609745444055 327846974442273914618166083)
        ·
          refine ⟨491770461663410871927249125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327846974442273914618166083 491770461663410871927249125)
          ·
            refine ⟨92206961561889538486359211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 491770461663410871927249125 92206961561889538486359211)
            ·
              refine ⟨138310442342834307729538817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92206961561889538486359211 138310442342834307729538817)
              ·
                refine ⟨103732831757125730797154113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138310442342834307729538817 103732831757125730797154113)
                ·
                  refine ⟨77799623817844298097865585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103732831757125730797154113 77799623817844298097865585)
                  ·
                    refine ⟨58349717863383223573399189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77799623817844298097865585 58349717863383223573399189)
                    ·
                      refine ⟨2735143024846088605003087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58349717863383223573399189 2735143024846088605003087)
                      ·
                        rfl

theorem cell23_5326672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_5326672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326672 prefixEnd_5326672 := by exact prefixLift 5326672
  have htrace : WordTrace (prefixWord ++ tailWord_5326672) baseStart_5326672 baseEnd_5326672 := by
    simpa [prefixWord, tailWord_5326672, baseEnd_5326672] using wordTrace_append hprefix tailTrace_5326672
  have hstable : (prefixWord ++ tailWord_5326672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326672).length < 2 ^ (prefixWord ++ tailWord_5326672).sum := by decide
  have hdescent : baseEnd_5326672 < baseStart_5326672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326673 : List Nat := [1, 2, 2, 1, 5, 3, 1, 2, 2, 4]
def baseStart_5326673 : Nat := 118140960795 + 5326673 * 2 ^ 59
def prefixEnd_5326673 : Nat := 4983230072969 + 3 ^ 40 * 5326673 * 2
def baseEnd_5326673 : Nat := 911714512775581033696861

theorem tailTrace_5326673 : CollatzResearch.WordTrace tailWord_5326673 prefixEnd_5326673 911714512775581033696861 := by
  unfold tailWord_5326673
  simp only [CollatzResearch.WordTrace]
  refine ⟨194279725031380919166736673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129519816687587279444491115 194279725031380919166736673)
  ·
    refine ⟨145709793773535689375052505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194279725031380919166736673 145709793773535689375052505)
    ·
      refine ⟨109282345330151767031289379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145709793773535689375052505 109282345330151767031289379)
      ·
        refine ⟨163923517995227650546934069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109282345330151767031289379 163923517995227650546934069)
        ·
          refine ⟨15367829812052592238775069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163923517995227650546934069 15367829812052592238775069)
          ·
            refine ⟨5762936179519722089540651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15367829812052592238775069 5762936179519722089540651)
            ·
              refine ⟨8644404269279583134310977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5762936179519722089540651 8644404269279583134310977)
              ·
                refine ⟨6483303201959687350733233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8644404269279583134310977 6483303201959687350733233)
                ·
                  refine ⟨4862477401469765513049925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6483303201959687350733233 4862477401469765513049925)
                  ·
                    refine ⟨911714512775581033696861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4862477401469765513049925 911714512775581033696861)
                    ·
                      rfl

theorem cell23_5326673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_5326673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326673 prefixEnd_5326673 := by exact prefixLift 5326673
  have htrace : WordTrace (prefixWord ++ tailWord_5326673) baseStart_5326673 baseEnd_5326673 := by
    simpa [prefixWord, tailWord_5326673, baseEnd_5326673] using wordTrace_append hprefix tailTrace_5326673
  have hstable : (prefixWord ++ tailWord_5326673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326673).length < 2 ^ (prefixWord ++ tailWord_5326673).sum := by decide
  have hdescent : baseEnd_5326673 < baseStart_5326673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326690 : List Nat := [3, 3, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_5326690 : Nat := 118140960795 + 5326690 * 2 ^ 59
def prefixEnd_5326690 : Nat := 4983230072969 + 3 ^ 40 * 5326690 * 2
def baseEnd_5326690 : Nat := 911717422499289844859335

theorem tailTrace_5326690 : CollatzResearch.WordTrace tailWord_5326690 prefixEnd_5326690 911717422499289844859335 := by
  unfold tailWord_5326690
  simp only [CollatzResearch.WordTrace]
  refine ⟨48570086268079832767526381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129520230048212887380070349 48570086268079832767526381)
  ·
    refine ⟨18213782350529937287822393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48570086268079832767526381 18213782350529937287822393)
    ·
      refine ⟨13660336762897452965866795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18213782350529937287822393 13660336762897452965866795)
      ·
        refine ⟨20490505144346179448800193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13660336762897452965866795 20490505144346179448800193)
        ·
          refine ⟨15367878858259634586600145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20490505144346179448800193 15367878858259634586600145)
          ·
            refine ⟨11525909143694725939950109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15367878858259634586600145 11525909143694725939950109)
            ·
              refine ⟨4322215928885522227481291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11525909143694725939950109 4322215928885522227481291)
              ·
                refine ⟨6483323893328283341221937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4322215928885522227481291 6483323893328283341221937)
                ·
                  refine ⟨4862492919996212505916453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6483323893328283341221937 4862492919996212505916453)
                  ·
                    refine ⟨911717422499289844859335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4862492919996212505916453 911717422499289844859335)
                    ·
                      rfl

theorem cell23_5326690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_5326690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326690 prefixEnd_5326690 := by exact prefixLift 5326690
  have htrace : WordTrace (prefixWord ++ tailWord_5326690) baseStart_5326690 baseEnd_5326690 := by
    simpa [prefixWord, tailWord_5326690, baseEnd_5326690] using wordTrace_append hprefix tailTrace_5326690
  have hstable : (prefixWord ++ tailWord_5326690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326690).length < 2 ^ (prefixWord ++ tailWord_5326690).sum := by decide
  have hdescent : baseEnd_5326690 < baseStart_5326690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326709 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_5326709 : Nat := 118140960795 + 5326709 * 2 ^ 59
def prefixEnd_5326709 : Nat := 4983230072969 + 3 ^ 40 * 5326709 * 2
def baseEnd_5326709 : Nat := 2735162023630304960240417

theorem tailTrace_5326709 : CollatzResearch.WordTrace tailWord_5326709 prefixEnd_5326709 2735162023630304960240417 := by
  unfold tailWord_5326709
  simp only [CollatzResearch.WordTrace]
  refine ⟨194281038059250497315047181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129520692039500331543364787 194281038059250497315047181)
  ·
    refine ⟨72855389272218936493142693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194281038059250497315047181 72855389272218936493142693)
    ·
      refine ⟨13660385488541050592464255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72855389272218936493142693 13660385488541050592464255)
      ·
        refine ⟨20490578232811575888696383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13660385488541050592464255 20490578232811575888696383)
        ·
          refine ⟨30735867349217363833044575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20490578232811575888696383 30735867349217363833044575)
          ·
            refine ⟨46103801023826045749566863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30735867349217363833044575 46103801023826045749566863)
            ·
              refine ⟨69155701535739068624350295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46103801023826045749566863 69155701535739068624350295)
              ·
                refine ⟨103733552303608602936525443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69155701535739068624350295 103733552303608602936525443)
                ·
                  refine ⟨155600328455412904404788165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103733552303608602936525443 155600328455412904404788165)
                  ·
                    refine ⟨29175061585389919575897781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 155600328455412904404788165 29175061585389919575897781)
                    ·
                      refine ⟨2735162023630304960240417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29175061585389919575897781 2735162023630304960240417)
                      ·
                        rfl

theorem cell23_5326709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_5326709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326709 prefixEnd_5326709 := by exact prefixLift 5326709
  have htrace : WordTrace (prefixWord ++ tailWord_5326709) baseStart_5326709 baseEnd_5326709 := by
    simpa [prefixWord, tailWord_5326709, baseEnd_5326709] using wordTrace_append hprefix tailTrace_5326709
  have hstable : (prefixWord ++ tailWord_5326709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326709).length < 2 ^ (prefixWord ++ tailWord_5326709).sum := by decide
  have hdescent : baseEnd_5326709 < baseStart_5326709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326723 : List Nat := [1, 1, 1, 3, 4, 2, 2, 3, 1, 3, 2]
def baseStart_5326723 : Nat := 118140960795 + 5326723 * 2 ^ 59
def prefixEnd_5326723 : Nat := 4983230072969 + 3 ^ 40 * 5326723 * 2
def baseEnd_5326723 : Nat := 2735169212359467905465353

theorem tailTrace_5326723 : CollatzResearch.WordTrace tailWord_5326723 prefixEnd_5326723 2735169212359467905465353 := by
  unfold tailWord_5326723
  simp only [CollatzResearch.WordTrace]
  refine ⟨194281548681199777706056823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129521032454133185137371215 194281548681199777706056823)
  ·
    refine ⟨291422323021799666559085235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194281548681199777706056823 291422323021799666559085235)
    ·
      refine ⟨437133484532699499838627853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291422323021799666559085235 437133484532699499838627853)
      ·
        refine ⟨163925056699762312439485445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 437133484532699499838627853 163925056699762312439485445)
        ·
          refine ⟨30735948131205433582403521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163925056699762312439485445 30735948131205433582403521)
          ·
            refine ⟨23051961098404075186802641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30735948131205433582403521 23051961098404075186802641)
            ·
              refine ⟨17288970823803056390101981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23051961098404075186802641 17288970823803056390101981)
              ·
                refine ⟨6483364058926146146288243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17288970823803056390101981 6483364058926146146288243)
                ·
                  refine ⟨9725046088389219219432365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6483364058926146146288243 9725046088389219219432365)
                  ·
                    refine ⟨3646892283145957207287137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9725046088389219219432365 3646892283145957207287137)
                    ·
                      refine ⟨2735169212359467905465353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3646892283145957207287137 2735169212359467905465353)
                      ·
                        rfl

theorem cell23_5326723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 3, 2].length) (baseStart_5326723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326723 prefixEnd_5326723 := by exact prefixLift 5326723
  have htrace : WordTrace (prefixWord ++ tailWord_5326723) baseStart_5326723 baseEnd_5326723 := by
    simpa [prefixWord, tailWord_5326723, baseEnd_5326723] using wordTrace_append hprefix tailTrace_5326723
  have hstable : (prefixWord ++ tailWord_5326723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326723).length < 2 ^ (prefixWord ++ tailWord_5326723).sum := by decide
  have hdescent : baseEnd_5326723 < baseStart_5326723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326776 : List Nat := [2, 1, 2, 1, 2, 3, 2, 5, 5]
def baseStart_5326776 : Nat := 118140960795 + 5326776 * 2 ^ 59
def prefixEnd_5326776 : Nat := 4983230072969 + 3 ^ 40 * 5326776 * 2
def baseEnd_5326776 : Nat := 303910714092684022011401

theorem tailTrace_5326776 : CollatzResearch.WordTrace tailWord_5326776 prefixEnd_5326776 303910714092684022011401 := by
  unfold tailWord_5326776
  simp only [CollatzResearch.WordTrace]
  refine ⟨97141740875003883878868091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129522321166671845171824121 97141740875003883878868091)
  ·
    refine ⟨145712611312505825818302137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97141740875003883878868091 145712611312505825818302137)
    ·
      refine ⟨109284458484379369363726603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145712611312505825818302137 109284458484379369363726603)
      ·
        refine ⟨163926687726569054045589905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109284458484379369363726603 163926687726569054045589905)
        ·
          refine ⟨122945015794926790534192429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163926687726569054045589905 122945015794926790534192429)
          ·
            refine ⟨46104380923097546450322161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122945015794926790534192429 46104380923097546450322161)
            ·
              refine ⟨34578285692323159837741621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46104380923097546450322161 34578285692323159837741621)
              ·
                refine ⟨3241714283655296234788277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34578285692323159837741621 3241714283655296234788277)
                ·
                  refine ⟨303910714092684022011401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3241714283655296234788277 303910714092684022011401)
                  ·
                    rfl

theorem cell23_5326776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 5].length) (baseStart_5326776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326776 prefixEnd_5326776 := by exact prefixLift 5326776
  have htrace : WordTrace (prefixWord ++ tailWord_5326776) baseStart_5326776 baseEnd_5326776 := by
    simpa [prefixWord, tailWord_5326776, baseEnd_5326776] using wordTrace_append hprefix tailTrace_5326776
  have hstable : (prefixWord ++ tailWord_5326776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326776).length < 2 ^ (prefixWord ++ tailWord_5326776).sum := by decide
  have hdescent : baseEnd_5326776 < baseStart_5326776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326789 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 4, 5]
def baseStart_5326789 : Nat := 118140960795 + 5326789 * 2 ^ 59
def prefixEnd_5326789 : Nat := 4983230072969 + 3 ^ 40 * 5326789 * 2
def baseEnd_5326789 : Nat := 911734367360888215746683

theorem tailTrace_5326789 : CollatzResearch.WordTrace tailWord_5326789 prefixEnd_5326789 911734367360888215746683 := by
  unfold tailWord_5326789
  simp only [CollatzResearch.WordTrace]
  refine ⟨194283955898960670977959421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129522637265973780651972947 194283955898960670977959421)
  ·
    refine ⟨72856483462110251616734783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194283955898960670977959421 72856483462110251616734783)
    ·
      refine ⟨109284725193165377425102175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72856483462110251616734783 109284725193165377425102175)
      ·
        refine ⟨163927087789748066137653263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109284725193165377425102175 163927087789748066137653263)
        ·
          refine ⟨245890631684622099206479895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163927087789748066137653263 245890631684622099206479895)
          ·
            refine ⟨368835947526933148809719843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245890631684622099206479895 368835947526933148809719843)
            ·
              refine ⟨553253921290399723214579765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368835947526933148809719843 553253921290399723214579765)
              ·
                refine ⟨51867555120974974051366853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 553253921290399723214579765 51867555120974974051366853)
                ·
                  refine ⟨9725166585182807634631285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51867555120974974051366853 9725166585182807634631285)
                  ·
                    refine ⟨911734367360888215746683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9725166585182807634631285 911734367360888215746683)
                    ·
                      rfl

theorem cell23_5326789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_5326789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326789 prefixEnd_5326789 := by exact prefixLift 5326789
  have htrace : WordTrace (prefixWord ++ tailWord_5326789) baseStart_5326789 baseEnd_5326789 := by
    simpa [prefixWord, tailWord_5326789, baseEnd_5326789] using wordTrace_append hprefix tailTrace_5326789
  have hstable : (prefixWord ++ tailWord_5326789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326789).length < 2 ^ (prefixWord ++ tailWord_5326789).sum := by decide
  have hdescent : baseEnd_5326789 < baseStart_5326789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326799 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 5]
def baseStart_5326799 : Nat := 118140960795 + 5326799 * 2 ^ 59
def prefixEnd_5326799 : Nat := 4983230072969 + 3 ^ 40 * 5326799 * 2
def baseEnd_5326799 : Nat := 2735208236889209608115003

theorem tailTrace_5326799 : CollatzResearch.WordTrace tailWord_5326799 prefixEnd_5326799 2735208236889209608115003 := by
  unfold tailWord_5326799
  simp only [CollatzResearch.WordTrace]
  refine ⟨194284320628924442685823451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129522880419282961790548967 194284320628924442685823451)
  ·
    refine ⟨291426480943386664028735177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194284320628924442685823451 291426480943386664028735177)
    ·
      refine ⟨218569860707539998021551383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291426480943386664028735177 218569860707539998021551383)
      ·
        refine ⟨327854791061309997032327075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218569860707539998021551383 327854791061309997032327075)
        ·
          refine ⟨491782186591964995548490613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327854791061309997032327075 491782186591964995548490613)
          ·
            refine ⟨46104579992996718332670995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 491782186591964995548490613 46104579992996718332670995)
            ·
              refine ⟨69156869989495077499006493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46104579992996718332670995 69156869989495077499006493)
              ·
                refine ⟨25933826246060654062127435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69156869989495077499006493 25933826246060654062127435)
                ·
                  refine ⟨38900739369090981093191153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25933826246060654062127435 38900739369090981093191153)
                  ·
                    refine ⟨29175554526818235819893365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38900739369090981093191153 29175554526818235819893365)
                    ·
                      refine ⟨2735208236889209608115003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29175554526818235819893365 2735208236889209608115003)
                      ·
                        rfl

theorem cell23_5326799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_5326799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326799 prefixEnd_5326799 := by exact prefixLift 5326799
  have htrace : WordTrace (prefixWord ++ tailWord_5326799) baseStart_5326799 baseEnd_5326799 := by
    simpa [prefixWord, tailWord_5326799, baseEnd_5326799] using wordTrace_append hprefix tailTrace_5326799
  have hstable : (prefixWord ++ tailWord_5326799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326799).length < 2 ^ (prefixWord ++ tailWord_5326799).sum := by decide
  have hdescent : baseEnd_5326799 < baseStart_5326799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326826 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_5326826 : Nat := 118140960795 + 5326826 * 2 ^ 59
def prefixEnd_5326826 : Nat := 4983230072969 + 3 ^ 40 * 5326826 * 2
def baseEnd_5326826 : Nat := 2735222100866881002477379

theorem tailTrace_5326826 : CollatzResearch.WordTrace tailWord_5326826 prefixEnd_5326826 2735222100866881002477379 := by
  unfold tailWord_5326826
  simp only [CollatzResearch.WordTrace]
  refine ⟨48571326349956656574264083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129523536933217750864704221 48571326349956656574264083)
  ·
    refine ⟨72856989524934984861396125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48571326349956656574264083 72856989524934984861396125)
    ·
      refine ⟨27321371071850619323023547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72856989524934984861396125 27321371071850619323023547)
      ·
        refine ⟨40982056607775928984535321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27321371071850619323023547 40982056607775928984535321)
        ·
          refine ⟨30736542455831946738401491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40982056607775928984535321 30736542455831946738401491)
          ·
            refine ⟨46104813683747920107602237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30736542455831946738401491 46104813683747920107602237)
            ·
              refine ⟨17289305131405470040350839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46104813683747920107602237 17289305131405470040350839)
              ·
                refine ⟨25933957697108205060526259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17289305131405470040350839 25933957697108205060526259)
                ·
                  refine ⟨38900936545662307590789389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25933957697108205060526259 38900936545662307590789389)
                  ·
                    refine ⟨14587851204623365346546021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38900936545662307590789389 14587851204623365346546021)
                    ·
                      refine ⟨2735222100866881002477379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14587851204623365346546021 2735222100866881002477379)
                      ·
                        rfl

theorem cell23_5326826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_5326826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326826 prefixEnd_5326826 := by exact prefixLift 5326826
  have htrace : WordTrace (prefixWord ++ tailWord_5326826) baseStart_5326826 baseEnd_5326826 := by
    simpa [prefixWord, tailWord_5326826, baseEnd_5326826] using wordTrace_append hprefix tailTrace_5326826
  have hstable : (prefixWord ++ tailWord_5326826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326826).length < 2 ^ (prefixWord ++ tailWord_5326826).sum := by decide
  have hdescent : baseEnd_5326826 < baseStart_5326826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326839 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 4]
def baseStart_5326839 : Nat := 118140960795 + 5326839 * 2 ^ 59
def prefixEnd_5326839 : Nat := 4983230072969 + 3 ^ 40 * 5326839 * 2
def baseEnd_5326839 : Nat := 2735228776115389451614819

theorem tailTrace_5326839 : CollatzResearch.WordTrace tailWord_5326839 prefixEnd_5326839 2735228776115389451614819 := by
  unfold tailWord_5326839
  simp only [CollatzResearch.WordTrace]
  refine ⟨194285779548779529517279571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129523853032519686344853047 194285779548779529517279571)
  ·
    refine ⟨291428669323169294275919357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194285779548779529517279571 291428669323169294275919357)
    ·
      refine ⟨109285750996188485353469759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291428669323169294275919357 109285750996188485353469759)
      ·
        refine ⟨163928626494282728030204639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109285750996188485353469759 163928626494282728030204639)
        ·
          refine ⟨245892939741424092045306959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163928626494282728030204639 245892939741424092045306959)
          ·
            refine ⟨368839409612136138067960439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245892939741424092045306959 368839409612136138067960439)
            ·
              refine ⟨553259114418204207101940659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368839409612136138067960439 553259114418204207101940659)
              ·
                refine ⟨829888671627306310652910989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553259114418204207101940659 829888671627306310652910989)
                ·
                  refine ⟨311208251860239866494841621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 829888671627306310652910989 311208251860239866494841621)
                  ·
                    refine ⟨14587886805948743741945701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 311208251860239866494841621 14587886805948743741945701)
                    ·
                      refine ⟨2735228776115389451614819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14587886805948743741945701 2735228776115389451614819)
                      ·
                        rfl

theorem cell23_5326839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_5326839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326839 prefixEnd_5326839 := by exact prefixLift 5326839
  have htrace : WordTrace (prefixWord ++ tailWord_5326839) baseStart_5326839 baseEnd_5326839 := by
    simpa [prefixWord, tailWord_5326839, baseEnd_5326839] using wordTrace_append hprefix tailTrace_5326839
  have hstable : (prefixWord ++ tailWord_5326839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326839).length < 2 ^ (prefixWord ++ tailWord_5326839).sum := by decide
  have hdescent : baseEnd_5326839 < baseStart_5326839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326853 : List Nat := [1, 3, 1, 1, 2, 5, 2, 1, 3, 4]
def baseStart_5326853 : Nat := 118140960795 + 5326853 * 2 ^ 59
def prefixEnd_5326853 : Nat := 4983230072969 + 3 ^ 40 * 5326853 * 2
def baseEnd_5326853 : Nat := 911745321614850798946585

theorem tailTrace_5326853 : CollatzResearch.WordTrace tailWord_5326853 prefixEnd_5326853 911745321614850798946585 := by
  unfold tailWord_5326853
  simp only [CollatzResearch.WordTrace]
  refine ⟨194286290170728809908289213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129524193447152539938859475 194286290170728809908289213)
  ·
    refine ⟨72857358814023303715608455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194286290170728809908289213 72857358814023303715608455)
    ·
      refine ⟨109286038221034955573412683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72857358814023303715608455 109286038221034955573412683)
      ·
        refine ⟨163929057331552433360119025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109286038221034955573412683 163929057331552433360119025)
        ·
          refine ⟨122946792998664325020089269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163929057331552433360119025 122946792998664325020089269)
          ·
            refine ⟨11526261843624780470633369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122946792998664325020089269 11526261843624780470633369)
            ·
              refine ⟨8644696382718585352975027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11526261843624780470633369 8644696382718585352975027)
              ·
                refine ⟨12967044574077878029462541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8644696382718585352975027 12967044574077878029462541)
                ·
                  refine ⟨4862641715279204261048453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12967044574077878029462541 4862641715279204261048453)
                  ·
                    refine ⟨911745321614850798946585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4862641715279204261048453 911745321614850798946585)
                    ·
                      rfl

theorem cell23_5326853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_5326853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326853 prefixEnd_5326853 := by exact prefixLift 5326853
  have htrace : WordTrace (prefixWord ++ tailWord_5326853) baseStart_5326853 baseEnd_5326853 := by
    simpa [prefixWord, tailWord_5326853, baseEnd_5326853] using wordTrace_append hprefix tailTrace_5326853
  have hstable : (prefixWord ++ tailWord_5326853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326853).length < 2 ^ (prefixWord ++ tailWord_5326853).sum := by decide
  have hdescent : baseEnd_5326853 < baseStart_5326853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326889 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 6, 1, 7]
def baseStart_5326889 : Nat := 118140960795 + 5326889 * 2 ^ 59
def prefixEnd_5326889 : Nat := 4983230072969 + 3 ^ 40 * 5326889 * 2
def baseEnd_5326889 : Nat := 2735254450148114255989589

theorem tailTrace_5326889 : CollatzResearch.WordTrace tailWord_5326889 prefixEnd_5326889 2735254450148114255989589 := by
  unfold tailWord_5326889
  simp only [CollatzResearch.WordTrace]
  refine ⟨194287603198598388056599721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129525068799065592037733147 194287603198598388056599721)
  ·
    refine ⟨145715702398948791042449791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194287603198598388056599721 145715702398948791042449791)
    ·
      refine ⟨218573553598423186563674687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145715702398948791042449791 218573553598423186563674687)
      ·
        refine ⟨327860330397634779845512031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218573553598423186563674687 327860330397634779845512031)
        ·
          refine ⟨491790495596452169768268047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327860330397634779845512031 491790495596452169768268047)
          ·
            refine ⟨737685743394678254652402071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491790495596452169768268047 737685743394678254652402071)
            ·
              refine ⟨1106528615092017381978603107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737685743394678254652402071 1106528615092017381978603107)
              ·
                refine ⟨1659792922638026072967904661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1106528615092017381978603107 1659792922638026072967904661)
                ·
                  refine ⟨77802793248657472170370531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1659792922638026072967904661 77802793248657472170370531)
                  ·
                    refine ⟨116704189872986208255555797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77802793248657472170370531 116704189872986208255555797)
                    ·
                      refine ⟨2735254450148114255989589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116704189872986208255555797 2735254450148114255989589)
                      ·
                        rfl

theorem cell23_5326889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_5326889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326889 prefixEnd_5326889 := by exact prefixLift 5326889
  have htrace : WordTrace (prefixWord ++ tailWord_5326889) baseStart_5326889 baseEnd_5326889 := by
    simpa [prefixWord, tailWord_5326889, baseEnd_5326889] using wordTrace_append hprefix tailTrace_5326889
  have hstable : (prefixWord ++ tailWord_5326889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326889).length < 2 ^ (prefixWord ++ tailWord_5326889).sum := by decide
  have hdescent : baseEnd_5326889 < baseStart_5326889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326903 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 4, 3, 2]
def baseStart_5326903 : Nat := 118140960795 + 5326903 * 2 ^ 59
def prefixEnd_5326903 : Nat := 4983230072969 + 3 ^ 40 * 5326903 * 2
def baseEnd_5326903 : Nat := 2735261638877277201214525

theorem tailTrace_5326903 : CollatzResearch.WordTrace tailWord_5326903 prefixEnd_5326903 2735261638877277201214525 := by
  unfold tailWord_5326903
  simp only [CollatzResearch.WordTrace]
  refine ⟨194288113820547668447609363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129525409213698445631739575 194288113820547668447609363)
  ·
    refine ⟨291432170730821502671414045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194288113820547668447609363 291432170730821502671414045)
    ·
      refine ⟨109287064024058063501780267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291432170730821502671414045 109287064024058063501780267)
      ·
        refine ⟨163930596036087095252670401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109287064024058063501780267 163930596036087095252670401)
        ·
          refine ⟨122947947027065321439502801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163930596036087095252670401 122947947027065321439502801)
          ·
            refine ⟨92210960270298991079627101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122947947027065321439502801 92210960270298991079627101)
            ·
              refine ⟨34579110101362121654860163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92210960270298991079627101 34579110101362121654860163)
              ·
                refine ⟨51868665152043182482290245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34579110101362121654860163 51868665152043182482290245)
                ·
                  refine ⟨9725374716008096715429421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51868665152043182482290245 9725374716008096715429421)
                  ·
                    refine ⟨3647015518503036268286033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9725374716008096715429421 3647015518503036268286033)
                    ·
                      refine ⟨2735261638877277201214525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3647015518503036268286033 2735261638877277201214525)
                      ·
                        rfl

theorem cell23_5326903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 3, 2].length) (baseStart_5326903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326903 prefixEnd_5326903 := by exact prefixLift 5326903
  have htrace : WordTrace (prefixWord ++ tailWord_5326903) baseStart_5326903 baseEnd_5326903 := by
    simpa [prefixWord, tailWord_5326903, baseEnd_5326903] using wordTrace_append hprefix tailTrace_5326903
  have hstable : (prefixWord ++ tailWord_5326903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326903).length < 2 ^ (prefixWord ++ tailWord_5326903).sum := by decide
  have hdescent : baseEnd_5326903 < baseStart_5326903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326933 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_5326933 : Nat := 118140960795 + 5326933 * 2 ^ 59
def prefixEnd_5326933 : Nat := 4983230072969 + 3 ^ 40 * 5326933 * 2
def baseEnd_5326933 : Nat := 2735277043296912083839387

theorem tailTrace_5326933 : CollatzResearch.WordTrace tailWord_5326933 prefixEnd_5326933 2735277043296912083839387 := by
  unfold tailWord_5326933
  simp only [CollatzResearch.WordTrace]
  refine ⟨194289208010438983571201453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129526138673625989047467635 194289208010438983571201453)
  ·
    refine ⟨72858453003914618839200545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194289208010438983571201453 72858453003914618839200545)
    ·
      refine ⟨54643839752935964129400409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72858453003914618839200545 54643839752935964129400409)
      ·
        refine ⟨40982879814701973097050307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54643839752935964129400409 40982879814701973097050307)
        ·
          refine ⟨61474319722052959645575461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40982879814701973097050307 61474319722052959645575461)
          ·
            refine ⟨11526434947884929933545399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61474319722052959645575461 11526434947884929933545399)
            ·
              refine ⟨17289652421827394900318099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11526434947884929933545399 17289652421827394900318099)
              ·
                refine ⟨25934478632741092350477149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17289652421827394900318099 25934478632741092350477149)
                ·
                  refine ⟨9725429487277909631428931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25934478632741092350477149 9725429487277909631428931)
                  ·
                    refine ⟨14588144230916864447143397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9725429487277909631428931 14588144230916864447143397)
                    ·
                      refine ⟨2735277043296912083839387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14588144230916864447143397 2735277043296912083839387)
                      ·
                        rfl

theorem cell23_5326933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_5326933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326933 prefixEnd_5326933 := by exact prefixLift 5326933
  have htrace : WordTrace (prefixWord ++ tailWord_5326933) baseStart_5326933 baseEnd_5326933 := by
    simpa [prefixWord, tailWord_5326933, baseEnd_5326933] using wordTrace_append hprefix tailTrace_5326933
  have hstable : (prefixWord ++ tailWord_5326933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326933).length < 2 ^ (prefixWord ++ tailWord_5326933).sum := by decide
  have hdescent : baseEnd_5326933 < baseStart_5326933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326960 : List Nat := [2, 1, 1, 1, 5, 3, 2, 2, 2, 4]
def baseStart_5326960 : Nat := 118140960795 + 5326960 * 2 ^ 59
def prefixEnd_5326960 : Nat := 4983230072969 + 3 ^ 40 * 5326960 * 2
def baseEnd_5326960 : Nat := 911763635758194492733921

theorem tailTrace_5326960 : CollatzResearch.WordTrace tailWord_5326960 prefixEnd_5326960 911763635758194492733921 := by
  unfold tailWord_5326960
  simp only [CollatzResearch.WordTrace]
  refine ⟨97145096390670583591217167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129526795187560778121622889 97145096390670583591217167)
  ·
    refine ⟨145717644586005875386825751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97145096390670583591217167 145717644586005875386825751)
    ·
      refine ⟨218576466879008813080238627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145717644586005875386825751 218576466879008813080238627)
      ·
        refine ⟨327864700318513219620357941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218576466879008813080238627 327864700318513219620357941)
        ·
          refine ⟨30737315654860614339408557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 327864700318513219620357941 30737315654860614339408557)
          ·
            refine ⟨11526493370572730377278209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30737315654860614339408557 11526493370572730377278209)
            ·
              refine ⟨8644870027929547782958657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11526493370572730377278209 8644870027929547782958657)
              ·
                refine ⟨6483652520947160837218993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8644870027929547782958657 6483652520947160837218993)
                ·
                  refine ⟨4862739390710370627914245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6483652520947160837218993 4862739390710370627914245)
                  ·
                    refine ⟨911763635758194492733921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4862739390710370627914245 911763635758194492733921)
                    ·
                      rfl

theorem cell23_5326960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 2, 4].length) (baseStart_5326960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326960 prefixEnd_5326960 := by exact prefixLift 5326960
  have htrace : WordTrace (prefixWord ++ tailWord_5326960) baseStart_5326960 baseEnd_5326960 := by
    simpa [prefixWord, tailWord_5326960, baseEnd_5326960] using wordTrace_append hprefix tailTrace_5326960
  have hstable : (prefixWord ++ tailWord_5326960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326960).length < 2 ^ (prefixWord ++ tailWord_5326960).sum := by decide
  have hdescent : baseEnd_5326960 < baseStart_5326960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326973 : List Nat := [1, 4, 1, 1, 3, 4, 1, 8]
def baseStart_5326973 : Nat := 118140960795 + 5326973 * 2 ^ 59
def prefixEnd_5326973 : Nat := 4983230072969 + 3 ^ 40 * 5326973 * 2
def baseEnd_5326973 : Nat := 101307317871225626938489

theorem tailTrace_5326973 : CollatzResearch.WordTrace tailWord_5326973 prefixEnd_5326973 101307317871225626938489 := by
  unfold tailWord_5326973
  simp only [CollatzResearch.WordTrace]
  refine ⟨194290666930294070402657573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129527111286862713601771715 194290666930294070402657573)
  ·
    refine ⟨36429500049430138200498295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194290666930294070402657573 36429500049430138200498295)
    ·
      refine ⟨54644250074145207300747443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36429500049430138200498295 54644250074145207300747443)
      ·
        refine ⟨81966375111217810951121165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54644250074145207300747443 81966375111217810951121165)
        ·
          refine ⟨30737390666706679106670437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81966375111217810951121165 30737390666706679106670437)
          ·
            refine ⟨5763260750007502332500707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30737390666706679106670437 5763260750007502332500707)
            ·
              refine ⟨8644891125011253498751061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5763260750007502332500707 8644891125011253498751061)
              ·
                refine ⟨101307317871225626938489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8644891125011253498751061 101307317871225626938489)
                ·
                  rfl

theorem cell23_5326973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 8].length) (baseStart_5326973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326973 prefixEnd_5326973 := by exact prefixLift 5326973
  have htrace : WordTrace (prefixWord ++ tailWord_5326973) baseStart_5326973 baseEnd_5326973 := by
    simpa [prefixWord, tailWord_5326973, baseEnd_5326973] using wordTrace_append hprefix tailTrace_5326973
  have hstable : (prefixWord ++ tailWord_5326973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326973).length < 2 ^ (prefixWord ++ tailWord_5326973).sum := by decide
  have hdescent : baseEnd_5326973 < baseStart_5326973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326983 : List Nat := [1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 3]
def baseStart_5326983 : Nat := 118140960795 + 5326983 * 2 ^ 59
def prefixEnd_5326983 : Nat := 4983230072969 + 3 ^ 40 * 5326983 * 2
def baseEnd_5326983 : Nat := 2735302717329636888214157

theorem tailTrace_5326983 : CollatzResearch.WordTrace tailWord_5326983 prefixEnd_5326983 2735302717329636888214157 := by
  unfold tailWord_5326983
  simp only [CollatzResearch.WordTrace]
  refine ⟨194291031660257842110521603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129527354440171894740347735 194291031660257842110521603)
  ·
    refine ⟨291436547490386763165782405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194291031660257842110521603 291436547490386763165782405)
    ·
      refine ⟨54644352654447518093584201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 291436547490386763165782405 54644352654447518093584201)
      ·
        refine ⟨40983264490835638570188151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54644352654447518093584201 40983264490835638570188151)
        ·
          refine ⟨61474896736253457855282227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40983264490835638570188151 61474896736253457855282227)
          ·
            refine ⟨92212345104380186782923341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61474896736253457855282227 92212345104380186782923341)
            ·
              refine ⟨34579629414142570043596253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92212345104380186782923341 34579629414142570043596253)
              ·
                refine ⟨12967361030303463766348595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34579629414142570043596253 12967361030303463766348595)
                ·
                  refine ⟨19451041545455195649522893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12967361030303463766348595 19451041545455195649522893)
                  ·
                    refine ⟨7294140579545698368571085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19451041545455195649522893 7294140579545698368571085)
                    ·
                      refine ⟨2735302717329636888214157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7294140579545698368571085 2735302717329636888214157)
                      ·
                        rfl

theorem cell23_5326983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_5326983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326983 prefixEnd_5326983 := by exact prefixLift 5326983
  have htrace : WordTrace (prefixWord ++ tailWord_5326983) baseStart_5326983 baseEnd_5326983 := by
    simpa [prefixWord, tailWord_5326983, baseEnd_5326983] using wordTrace_append hprefix tailTrace_5326983
  have hstable : (prefixWord ++ tailWord_5326983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326983).length < 2 ^ (prefixWord ++ tailWord_5326983).sum := by decide
  have hdescent : baseEnd_5326983 < baseStart_5326983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326990 : List Nat := [4, 1, 1, 3, 3, 1, 3, 7]
def baseStart_5326990 : Nat := 118140960795 + 5326990 * 2 ^ 59
def prefixEnd_5326990 : Nat := 4983230072969 + 3 ^ 40 * 5326990 * 2
def baseEnd_5326990 : Nat := 101307641173859939289875

theorem tailTrace_5326990 : CollatzResearch.WordTrace tailWord_5326990 prefixEnd_5326990 101307641173859939289875 := by
  unfold tailWord_5326990
  simp only [CollatzResearch.WordTrace]
  refine ⟨24286410871404060288253303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129527524647488321537350949 24286410871404060288253303)
  ·
    refine ⟨36429616307106090432379955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24286410871404060288253303 36429616307106090432379955)
    ·
      refine ⟨54644424460659135648569933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36429616307106090432379955 54644424460659135648569933)
      ·
        refine ⟨20491659172747175868213725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54644424460659135648569933 20491659172747175868213725)
        ·
          refine ⟨7684372189780190950580147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20491659172747175868213725 7684372189780190950580147)
          ·
            refine ⟨11526558284670286425870221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7684372189780190950580147 11526558284670286425870221)
            ·
              refine ⟨4322459356751357409701333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11526558284670286425870221 4322459356751357409701333)
              ·
                refine ⟨101307641173859939289875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4322459356751357409701333 101307641173859939289875)
                ·
                  rfl

theorem cell23_5326990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 7].length) (baseStart_5326990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326990 prefixEnd_5326990 := by exact prefixLift 5326990
  have htrace : WordTrace (prefixWord ++ tailWord_5326990) baseStart_5326990 baseEnd_5326990 := by
    simpa [prefixWord, tailWord_5326990, baseEnd_5326990] using wordTrace_append hprefix tailTrace_5326990
  have hstable : (prefixWord ++ tailWord_5326990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326990).length < 2 ^ (prefixWord ++ tailWord_5326990).sum := by decide
  have hdescent : baseEnd_5326990 < baseStart_5326990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327028 : List Nat := [2, 5, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_5327028 : Nat := 118140960795 + 5327028 * 2 ^ 59
def prefixEnd_5327028 : Nat := 4983230072969 + 3 ^ 40 * 5327028 * 2
def baseEnd_5327028 : Nat := 911775274653029737383817

theorem tailTrace_5327028 : CollatzResearch.WordTrace tailWord_5327028 prefixEnd_5327028 911775274653029737383817 := by
  unfold tailWord_5327028
  simp only [CollatzResearch.WordTrace]
  refine ⟨97146336472547407397954869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129528448630063209863939825 97146336472547407397954869)
  ·
    refine ⟨9107469044301319443558269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97146336472547407397954869 9107469044301319443558269)
    ·
      refine ⟨3415300891612994791334351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9107469044301319443558269 3415300891612994791334351)
      ·
        refine ⟨5122951337419492187001527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3415300891612994791334351 5122951337419492187001527)
        ·
          refine ⟨7684427006129238280502291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5122951337419492187001527 7684427006129238280502291)
          ·
            refine ⟨11526640509193857420753437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7684427006129238280502291 11526640509193857420753437)
            ·
              refine ⟨4322490190947696532782539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11526640509193857420753437 4322490190947696532782539)
              ·
                refine ⟨6483735286421544799173809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4322490190947696532782539 6483735286421544799173809)
                ·
                  refine ⟨4862801464816158599380357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6483735286421544799173809 4862801464816158599380357)
                  ·
                    refine ⟨911775274653029737383817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4862801464816158599380357 911775274653029737383817)
                    ·
                      rfl

theorem cell23_5327028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_5327028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327028 prefixEnd_5327028 := by exact prefixLift 5327028
  have htrace : WordTrace (prefixWord ++ tailWord_5327028) baseStart_5327028 baseEnd_5327028 := by
    simpa [prefixWord, tailWord_5327028, baseEnd_5327028] using wordTrace_append hprefix tailTrace_5327028
  have hstable : (prefixWord ++ tailWord_5327028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327028).length < 2 ^ (prefixWord ++ tailWord_5327028).sum := by decide
  have hdescent : baseEnd_5327028 < baseStart_5327028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327044 : List Nat := [2, 3, 3, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_5327044 : Nat := 118140960795 + 5327044 * 2 ^ 59
def prefixEnd_5327044 : Nat := 4983230072969 + 3 ^ 40 * 5327044 * 2
def baseEnd_5327044 : Nat := 2735334039649561149551377

theorem tailTrace_5327044 : CollatzResearch.WordTrace tailWord_5327044 prefixEnd_5327044 2735334039649561149551377 := by
  unfold tailWord_5327044
  simp only [CollatzResearch.WordTrace]
  refine ⟨97146628256518424764246093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129528837675357899685661457 97146628256518424764246093)
  ·
    refine ⟨36429985596194409286592285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97146628256518424764246093 36429985596194409286592285)
    ·
      refine ⟨13661244598572903482472107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36429985596194409286592285 13661244598572903482472107)
      ·
        refine ⟨20491866897859355223708161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13661244598572903482472107 20491866897859355223708161)
        ·
          refine ⟨15368900173394516417781121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20491866897859355223708161 15368900173394516417781121)
          ·
            refine ⟨11526675130045887313335841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15368900173394516417781121 11526675130045887313335841)
            ·
              refine ⟨8645006347534415485001881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11526675130045887313335841 8645006347534415485001881)
              ·
                refine ⟨6483754760650811613751411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8645006347534415485001881 6483754760650811613751411)
                ·
                  refine ⟨9725632140976217420627117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6483754760650811613751411 9725632140976217420627117)
                  ·
                    refine ⟨3647112052866081532735169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9725632140976217420627117 3647112052866081532735169)
                    ·
                      refine ⟨2735334039649561149551377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3647112052866081532735169 2735334039649561149551377)
                      ·
                        rfl

theorem cell23_5327044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_5327044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327044 prefixEnd_5327044 := by exact prefixLift 5327044
  have htrace : WordTrace (prefixWord ++ tailWord_5327044) baseStart_5327044 baseEnd_5327044 := by
    simpa [prefixWord, tailWord_5327044, baseEnd_5327044] using wordTrace_append hprefix tailTrace_5327044
  have hstable : (prefixWord ++ tailWord_5327044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327044).length < 2 ^ (prefixWord ++ tailWord_5327044).sum := by decide
  have hdescent : baseEnd_5327044 < baseStart_5327044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327080 : List Nat := [2, 1, 4, 1, 2, 4, 1, 1, 7]
def baseStart_5327080 : Nat := 118140960795 + 5327080 * 2 ^ 59
def prefixEnd_5327080 : Nat := 4983230072969 + 3 ^ 40 * 5327080 * 2
def baseEnd_5327080 : Nat := 303928058328124778744579

theorem tailTrace_5327080 : CollatzResearch.WordTrace tailWord_5327080 prefixEnd_5327080 303928058328124778744579 := by
  unfold tailWord_5327080
  simp only [CollatzResearch.WordTrace]
  refine ⟨97147284770453213838401347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129529713027270951784535129 97147284770453213838401347)
  ·
    refine ⟨145720927155679820757602021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97147284770453213838401347 145720927155679820757602021)
    ·
      refine ⟨27322673841689966392050379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145720927155679820757602021 27322673841689966392050379)
      ·
        refine ⟨40984010762534949588075569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27322673841689966392050379 40984010762534949588075569)
        ·
          refine ⟨30738008071901212191056677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40984010762534949588075569 30738008071901212191056677)
          ·
            refine ⟨5763376513481477285823127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30738008071901212191056677 5763376513481477285823127)
            ·
              refine ⟨8645064770222215928734691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5763376513481477285823127 8645064770222215928734691)
              ·
                refine ⟨12967597155333323893102037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8645064770222215928734691 12967597155333323893102037)
                ·
                  refine ⟨303928058328124778744579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12967597155333323893102037 303928058328124778744579)
                  ·
                    rfl

theorem cell23_5327080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 7].length) (baseStart_5327080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327080 prefixEnd_5327080 := by exact prefixLift 5327080
  have htrace : WordTrace (prefixWord ++ tailWord_5327080) baseStart_5327080 baseEnd_5327080 := by
    simpa [prefixWord, tailWord_5327080, baseEnd_5327080] using wordTrace_append hprefix tailTrace_5327080
  have hstable : (prefixWord ++ tailWord_5327080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327080).length < 2 ^ (prefixWord ++ tailWord_5327080).sum := by decide
  have hdescent : baseEnd_5327080 < baseStart_5327080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327134 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_5327134 : Nat := 118140960795 + 5327134 * 2 ^ 59
def prefixEnd_5327134 : Nat := 4983230072969 + 3 ^ 40 * 5327134 * 2
def baseEnd_5327134 : Nat := 2735380252908465797425963

theorem tailTrace_5327134 : CollatzResearch.WordTrace tailWord_5327134 prefixEnd_5327134 2735380252908465797425963 := by
  unfold tailWord_5327134
  simp only [CollatzResearch.WordTrace]
  refine ⟨24287067385338849362408557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129531026055140529932845637 24287067385338849362408557)
  ·
    refine ⟨9107650269502068510903209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24287067385338849362408557 9107650269502068510903209)
    ·
      refine ⟨6830737702126551383177407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9107650269502068510903209 6830737702126551383177407)
      ·
        refine ⟨10246106553189827074766111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6830737702126551383177407 10246106553189827074766111)
        ·
          refine ⟨15369159829784740612149167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10246106553189827074766111 15369159829784740612149167)
          ·
            refine ⟨23053739744677110918223751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15369159829784740612149167 23053739744677110918223751)
            ·
              refine ⟨34580609617015666377335627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23053739744677110918223751 34580609617015666377335627)
              ·
                refine ⟨51870914425523499566003441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34580609617015666377335627 51870914425523499566003441)
                ·
                  refine ⟨38903185819142624674502581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51870914425523499566003441 38903185819142624674502581)
                  ·
                    refine ⟨3647173670544621063234617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38903185819142624674502581 3647173670544621063234617)
                    ·
                      refine ⟨2735380252908465797425963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3647173670544621063234617 2735380252908465797425963)
                      ·
                        rfl

theorem cell23_5327134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_5327134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327134 prefixEnd_5327134 := by exact prefixLift 5327134
  have htrace : WordTrace (prefixWord ++ tailWord_5327134) baseStart_5327134 baseEnd_5327134 := by
    simpa [prefixWord, tailWord_5327134, baseEnd_5327134] using wordTrace_append hprefix tailTrace_5327134
  have hstable : (prefixWord ++ tailWord_5327134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327134).length < 2 ^ (prefixWord ++ tailWord_5327134).sum := by decide
  have hdescent : baseEnd_5327134 < baseStart_5327134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327183 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 5, 5]
def baseStart_5327183 : Nat := 118140960795 + 5327183 * 2 ^ 59
def prefixEnd_5327183 : Nat := 4983230072969 + 3 ^ 40 * 5327183 * 2
def baseEnd_5327183 : Nat := 911801804486845368571079

theorem tailTrace_5327183 : CollatzResearch.WordTrace tailWord_5327183 prefixEnd_5327183 911801804486845368571079 := by
  unfold tailWord_5327183
  simp only [CollatzResearch.WordTrace]
  refine ⟨194298326259533276267802203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129532217506355517511868135 194298326259533276267802203)
  ·
    refine ⟨291447489389299914401703305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194298326259533276267802203 291447489389299914401703305)
    ·
      refine ⟨218585617041974935801277479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291447489389299914401703305 218585617041974935801277479)
      ·
        refine ⟨327878425562962403701916219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218585617041974935801277479 327878425562962403701916219)
        ·
          refine ⟨491817638344443605552874329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327878425562962403701916219 491817638344443605552874329)
          ·
            refine ⟨368863228758332704164655747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 491817638344443605552874329 368863228758332704164655747)
            ·
              refine ⟨553294843137499056246983621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368863228758332704164655747 553294843137499056246983621)
              ·
                refine ⟨103742783088281073046309429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 553294843137499056246983621 103742783088281073046309429)
                ·
                  refine ⟨9725885914526350598091509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103742783088281073046309429 9725885914526350598091509)
                  ·
                    refine ⟨911801804486845368571079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9725885914526350598091509 911801804486845368571079)
                    ·
                      rfl

theorem cell23_5327183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 5].length) (baseStart_5327183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327183 prefixEnd_5327183 := by exact prefixLift 5327183
  have htrace : WordTrace (prefixWord ++ tailWord_5327183) baseStart_5327183 baseEnd_5327183 := by
    simpa [prefixWord, tailWord_5327183, baseEnd_5327183] using wordTrace_append hprefix tailTrace_5327183
  have hstable : (prefixWord ++ tailWord_5327183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327183).length < 2 ^ (prefixWord ++ tailWord_5327183).sum := by decide
  have hdescent : baseEnd_5327183 < baseStart_5327183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327207 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 1, 5, 2]
def baseStart_5327207 : Nat := 118140960795 + 5327207 * 2 ^ 59
def prefixEnd_5327207 : Nat := 4983230072969 + 3 ^ 40 * 5327207 * 2
def baseEnd_5327207 : Nat := 2735417736996244011813127

theorem tailTrace_5327207 : CollatzResearch.WordTrace tailWord_5327207 prefixEnd_5327207 2735417736996244011813127 := by
  unfold tailWord_5327207
  simp only [CollatzResearch.WordTrace]
  refine ⟨194299201611446328366675875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129532801074297552244450583 194299201611446328366675875)
  ·
    refine ⟨291448802417169492550013813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194299201611446328366675875 291448802417169492550013813)
    ·
      refine ⟨27323325226609639926563795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 291448802417169492550013813 27323325226609639926563795)
      ·
        refine ⟨40984987839914459889845693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27323325226609639926563795 40984987839914459889845693)
        ·
          refine ⟨15369370439967922458692135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40984987839914459889845693 15369370439967922458692135)
          ·
            refine ⟨23054055659951883688038203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15369370439967922458692135 23054055659951883688038203)
            ·
              refine ⟨34581083489927825532057305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23054055659951883688038203 34581083489927825532057305)
              ·
                refine ⟨25935812617445869149042979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34581083489927825532057305 25935812617445869149042979)
                ·
                  refine ⟨38903718926168803723564469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25935812617445869149042979 38903718926168803723564469)
                  ·
                    refine ⟨3647223649328325349084169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38903718926168803723564469 3647223649328325349084169)
                    ·
                      refine ⟨2735417736996244011813127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3647223649328325349084169 2735417736996244011813127)
                      ·
                        rfl

theorem cell23_5327207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_5327207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327207 prefixEnd_5327207 := by exact prefixLift 5327207
  have htrace : WordTrace (prefixWord ++ tailWord_5327207) baseStart_5327207 baseEnd_5327207 := by
    simpa [prefixWord, tailWord_5327207, baseEnd_5327207] using wordTrace_append hprefix tailTrace_5327207
  have hstable : (prefixWord ++ tailWord_5327207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327207).length < 2 ^ (prefixWord ++ tailWord_5327207).sum := by decide
  have hdescent : baseEnd_5327207 < baseStart_5327207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327243 : List Nat := [1, 1, 1, 1, 4, 4, 11]
def baseStart_5327243 : Nat := 118140960795 + 5327243 * 2 ^ 59
def prefixEnd_5327243 : Nat := 4983230072969 + 3 ^ 40 * 5327243 * 2
def baseEnd_5327243 : Nat := 33770817559256862604481

theorem tailTrace_5327243 : CollatzResearch.WordTrace tailWord_5327243 prefixEnd_5327243 33770817559256862604481 := by
  unfold tailWord_5327243
  simp only [CollatzResearch.WordTrace]
  refine ⟨194300514639315906514986383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129533676426210604343324255 194300514639315906514986383)
  ·
    refine ⟨291450771958973859772479575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194300514639315906514986383 291450771958973859772479575)
    ·
      refine ⟨437176157938460789658719363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291450771958973859772479575 437176157938460789658719363)
      ·
        refine ⟨655764236907691184488079045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437176157938460789658719363 655764236907691184488079045)
        ·
          refine ⟨122955794420192097091514821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 655764236907691184488079045 122955794420192097091514821)
          ·
            refine ⟨23054211453786018204659029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122955794420192097091514821 23054211453786018204659029)
            ·
              refine ⟨33770817559256862604481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23054211453786018204659029 33770817559256862604481)
              ·
                rfl

theorem cell23_5327243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 11].length) (baseStart_5327243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327243 prefixEnd_5327243 := by exact prefixLift 5327243
  have htrace : WordTrace (prefixWord ++ tailWord_5327243) baseStart_5327243 baseEnd_5327243 := by
    simpa [prefixWord, tailWord_5327243, baseEnd_5327243] using wordTrace_append hprefix tailTrace_5327243
  have hstable : (prefixWord ++ tailWord_5327243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327243).length < 2 ^ (prefixWord ++ tailWord_5327243).sum := by decide
  have hdescent : baseEnd_5327243 < baseStart_5327243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327264 : List Nat := [2, 1, 1, 4, 1, 3, 4, 1, 2, 4]
def baseStart_5327264 : Nat := 118140960795 + 5327264 * 2 ^ 59
def prefixEnd_5327264 : Nat := 4983230072969 + 3 ^ 40 * 5327264 * 2
def baseEnd_5327264 : Nat := 911815668464516762933455

theorem tailTrace_5327264 : CollatzResearch.WordTrace tailWord_5327264 prefixEnd_5327264 911815668464516762933455 := by
  unfold tailWord_5327264
  simp only [CollatzResearch.WordTrace]
  refine ⟨97150640286119913550750423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129534187048159884734333897 97150640286119913550750423)
  ·
    refine ⟨145725960429179870326125635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97150640286119913550750423 145725960429179870326125635)
    ·
      refine ⟨218588940643769805489188453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145725960429179870326125635 218588940643769805489188453)
      ·
        refine ⟨40985426370706838529222835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218588940643769805489188453 40985426370706838529222835)
        ·
          refine ⟨61478139556060257793834253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40985426370706838529222835 61478139556060257793834253)
          ·
            refine ⟨23054302333522596672687845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61478139556060257793834253 23054302333522596672687845)
            ·
              refine ⟨4322681687535486876128971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23054302333522596672687845 4322681687535486876128971)
              ·
                refine ⟨6484022531303230314193457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4322681687535486876128971 6484022531303230314193457)
                ·
                  refine ⟨4863016898477422735645093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6484022531303230314193457 4863016898477422735645093)
                  ·
                    refine ⟨911815668464516762933455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4863016898477422735645093 911815668464516762933455)
                    ·
                      rfl

theorem cell23_5327264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 2, 4].length) (baseStart_5327264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327264 prefixEnd_5327264 := by exact prefixLift 5327264
  have htrace : WordTrace (prefixWord ++ tailWord_5327264) baseStart_5327264 baseEnd_5327264 := by
    simpa [prefixWord, tailWord_5327264, baseEnd_5327264] using wordTrace_append hprefix tailTrace_5327264
  have hstable : (prefixWord ++ tailWord_5327264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327264).length < 2 ^ (prefixWord ++ tailWord_5327264).sum := by decide
  have hdescent : baseEnd_5327264 < baseStart_5327264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327287 : List Nat := [1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 3]
def baseStart_5327287 : Nat := 118140960795 + 5327287 * 2 ^ 59
def prefixEnd_5327287 : Nat := 4983230072969 + 3 ^ 40 * 5327287 * 2
def baseEnd_5327287 : Nat := 2735458815448603698812759

theorem tailTrace_5327287 : CollatzResearch.WordTrace tailWord_5327287 prefixEnd_5327287 2735458815448603698812759 := by
  unfold tailWord_5327287
  simp only [CollatzResearch.WordTrace]
  refine ⟨194302119451156502029588115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129534746300771001353058743 194302119451156502029588115)
  ·
    refine ⟨291453179176734753044382173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194302119451156502029588115 291453179176734753044382173)
    ·
      refine ⟨109294942191275532391643315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291453179176734753044382173 109294942191275532391643315)
      ·
        refine ⟨163942413286913298587464973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109294942191275532391643315 163942413286913298587464973)
        ·
          refine ⟨61478404982592486970299365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163942413286913298587464973 61478404982592486970299365)
          ·
            refine ⟨11527200934236091306931131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61478404982592486970299365 11527200934236091306931131)
            ·
              refine ⟨17290801401354136960396697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11527200934236091306931131 17290801401354136960396697)
              ·
                refine ⟨12968101051015602720297523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17290801401354136960396697 12968101051015602720297523)
                ·
                  refine ⟨19452151576523404080446285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12968101051015602720297523 19452151576523404080446285)
                  ·
                    refine ⟨7294556841196276530167357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19452151576523404080446285 7294556841196276530167357)
                    ·
                      refine ⟨2735458815448603698812759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7294556841196276530167357 2735458815448603698812759)
                      ·
                        rfl

theorem cell23_5327287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_5327287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327287 prefixEnd_5327287 := by exact prefixLift 5327287
  have htrace : WordTrace (prefixWord ++ tailWord_5327287) baseStart_5327287 baseEnd_5327287 := by
    simpa [prefixWord, tailWord_5327287, baseEnd_5327287] using wordTrace_append hprefix tailTrace_5327287
  have hstable : (prefixWord ++ tailWord_5327287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327287).length < 2 ^ (prefixWord ++ tailWord_5327287).sum := by decide
  have hdescent : baseEnd_5327287 < baseStart_5327287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327304 : List Nat := [2, 1, 3, 1, 3, 2, 1, 4, 2, 1, 3]
def baseStart_5327304 : Nat := 118140960795 + 5327304 * 2 ^ 59
def prefixEnd_5327304 : Nat := 4983230072969 + 3 ^ 40 * 5327304 * 2
def baseEnd_5327304 : Nat := 2735467544619730132300181

theorem tailTrace_5327304 : CollatzResearch.WordTrace tailWord_5327304 prefixEnd_5327304 2735467544619730132300181 := by
  unfold tailWord_5327304
  simp only [CollatzResearch.WordTrace]
  refine ⟨97151369746047456966478483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129535159661396609288637977 97151369746047456966478483)
  ·
    refine ⟨145727054619071185449717725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97151369746047456966478483 145727054619071185449717725)
    ·
      refine ⟨54647645482151694543644147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145727054619071185449717725 54647645482151694543644147)
      ·
        refine ⟨81971468223227541815466221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54647645482151694543644147 81971468223227541815466221)
        ·
          refine ⟨30739300583710328180799833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81971468223227541815466221 30739300583710328180799833)
          ·
            refine ⟨23054475437782746135599875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30739300583710328180799833 23054475437782746135599875)
            ·
              refine ⟨34581713156674119203399813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23054475437782746135599875 34581713156674119203399813)
              ·
                refine ⟨6484071216876397350637465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34581713156674119203399813 6484071216876397350637465)
                ·
                  refine ⟨4863053412657298012978099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6484071216876397350637465 4863053412657298012978099)
                  ·
                    refine ⟨7294580118985947019467149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4863053412657298012978099 7294580118985947019467149)
                    ·
                      refine ⟨2735467544619730132300181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7294580118985947019467149 2735467544619730132300181)
                      ·
                        rfl

theorem cell23_5327304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_5327304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327304 prefixEnd_5327304 := by exact prefixLift 5327304
  have htrace : WordTrace (prefixWord ++ tailWord_5327304) baseStart_5327304 baseEnd_5327304 := by
    simpa [prefixWord, tailWord_5327304, baseEnd_5327304] using wordTrace_append hprefix tailTrace_5327304
  have hstable : (prefixWord ++ tailWord_5327304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327304).length < 2 ^ (prefixWord ++ tailWord_5327304).sum := by decide
  have hdescent : baseEnd_5327304 < baseStart_5327304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327340 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 4]
def baseStart_5327340 : Nat := 118140960795 + 5327340 * 2 ^ 59
def prefixEnd_5327340 : Nat := 4983230072969 + 3 ^ 40 * 5327340 * 2
def baseEnd_5327340 : Nat := 2735486029923291991450015

theorem tailTrace_5327340 : CollatzResearch.WordTrace tailWord_5327340 prefixEnd_5327340 2735486029923291991450015 := by
  unfold tailWord_5327340
  simp only [CollatzResearch.WordTrace]
  refine ⟨97152026259982246040633737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129536035013309661387511649 97152026259982246040633737)
  ·
    refine ⟨72864019694986684530475303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97152026259982246040633737 72864019694986684530475303)
    ·
      refine ⟨109296029542480026795712955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72864019694986684530475303 109296029542480026795712955)
      ·
        refine ⟨163944044313720040193569433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109296029542480026795712955 163944044313720040193569433)
        ·
          refine ⟨122958033235290030145177075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163944044313720040193569433 122958033235290030145177075)
          ·
            refine ⟨184437049852935045217765613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122958033235290030145177075 184437049852935045217765613)
            ·
              refine ⟨69163893694850641956662105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184437049852935045217765613 69163893694850641956662105)
              ·
                refine ⟨51872920271137981467496579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69163893694850641956662105 51872920271137981467496579)
                ·
                  refine ⟨77809380406706972201244869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51872920271137981467496579 77809380406706972201244869)
                  ·
                    refine ⟨14589258826257557287733413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77809380406706972201244869 14589258826257557287733413)
                    ·
                      refine ⟨2735486029923291991450015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14589258826257557287733413 2735486029923291991450015)
                      ·
                        rfl

theorem cell23_5327340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_5327340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327340 prefixEnd_5327340 := by exact prefixLift 5327340
  have htrace : WordTrace (prefixWord ++ tailWord_5327340) baseStart_5327340 baseEnd_5327340 := by
    simpa [prefixWord, tailWord_5327340, baseEnd_5327340] using wordTrace_append hprefix tailTrace_5327340
  have hstable : (prefixWord ++ tailWord_5327340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327340).length < 2 ^ (prefixWord ++ tailWord_5327340).sum := by decide
  have hdescent : baseEnd_5327340 < baseStart_5327340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327344 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 4, 2, 2]
def baseStart_5327344 : Nat := 118140960795 + 5327344 * 2 ^ 59
def prefixEnd_5327344 : Nat := 4983230072969 + 3 ^ 40 * 5327344 * 2
def baseEnd_5327344 : Nat := 2735488083845909975799997

theorem tailTrace_5327344 : CollatzResearch.WordTrace tailWord_5327344 prefixEnd_5327344 2735488083845909975799997 := by
  unfold tailWord_5327344
  simp only [CollatzResearch.WordTrace]
  refine ⟨97152099205975000382206543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129536132274633333842942057 97152099205975000382206543)
  ·
    refine ⟨145728148808962500573309815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97152099205975000382206543 145728148808962500573309815)
    ·
      refine ⟨218592223213443750859964723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145728148808962500573309815 218592223213443750859964723)
      ·
        refine ⟨327888334820165626289947085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218592223213443750859964723 327888334820165626289947085)
        ·
          refine ⟨122958125557562109858730157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 327888334820165626289947085 122958125557562109858730157)
          ·
            refine ⟨46109297084085791197023809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122958125557562109858730157 46109297084085791197023809)
            ·
              refine ⟨34581972813064343397767857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46109297084085791197023809 34581972813064343397767857)
              ·
                refine ⟨25936479609798257548325893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34581972813064343397767857 25936479609798257548325893)
                ·
                  refine ⟨4863089926837173290311105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25936479609798257548325893 4863089926837173290311105)
                  ·
                    refine ⟨3647317445127879967733329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4863089926837173290311105 3647317445127879967733329)
                    ·
                      refine ⟨2735488083845909975799997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3647317445127879967733329 2735488083845909975799997)
                      ·
                        rfl

theorem cell23_5327344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 4, 2, 2].length) (baseStart_5327344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327344 prefixEnd_5327344 := by exact prefixLift 5327344
  have htrace : WordTrace (prefixWord ++ tailWord_5327344) baseStart_5327344 baseEnd_5327344 := by
    simpa [prefixWord, tailWord_5327344, baseEnd_5327344] using wordTrace_append hprefix tailTrace_5327344
  have hstable : (prefixWord ++ tailWord_5327344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327344).length < 2 ^ (prefixWord ++ tailWord_5327344).sum := by decide
  have hdescent : baseEnd_5327344 < baseStart_5327344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327361 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 4, 2, 2]
def baseStart_5327361 : Nat := 118140960795 + 5327361 * 2 ^ 59
def prefixEnd_5327361 : Nat := 4983230072969 + 3 ^ 40 * 5327361 * 2
def baseEnd_5327361 : Nat := 2735496813017036409287419

theorem tailTrace_5327361 : CollatzResearch.WordTrace tailWord_5327361 prefixEnd_5327361 2735496813017036409287419 := by
  unfold tailWord_5327361
  simp only [CollatzResearch.WordTrace]
  refine ⟨194304818452888412667781937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129536545635258941778521291 194304818452888412667781937)
  ·
    refine ⟨145728613839666309500836453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194304818452888412667781937 145728613839666309500836453)
    ·
      refine ⟨27324115094937433031406835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145728613839666309500836453 27324115094937433031406835)
      ·
        refine ⟨40986172642406149547110253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27324115094937433031406835 40986172642406149547110253)
        ·
          refine ⟨15369814740902306080166345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40986172642406149547110253 15369814740902306080166345)
          ·
            refine ⟨11527361055676729560124759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15369814740902306080166345 11527361055676729560124759)
            ·
              refine ⟨17291041583515094340187139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11527361055676729560124759 17291041583515094340187139)
              ·
                refine ⟨25936562375272641510280709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17291041583515094340187139 25936562375272641510280709)
                ·
                  refine ⟨4863105445363620283177633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25936562375272641510280709 4863105445363620283177633)
                  ·
                    refine ⟨3647329084022715212383225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4863105445363620283177633 3647329084022715212383225)
                    ·
                      refine ⟨2735496813017036409287419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3647329084022715212383225 2735496813017036409287419)
                      ·
                        rfl

theorem cell23_5327361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_5327361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327361 prefixEnd_5327361 := by exact prefixLift 5327361
  have htrace : WordTrace (prefixWord ++ tailWord_5327361) baseStart_5327361 baseEnd_5327361 := by
    simpa [prefixWord, tailWord_5327361, baseEnd_5327361] using wordTrace_append hprefix tailTrace_5327361
  have hstable : (prefixWord ++ tailWord_5327361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327361).length < 2 ^ (prefixWord ++ tailWord_5327361).sum := by decide
  have hdescent : baseEnd_5327361 < baseStart_5327361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327414 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_5327414 : Nat := 118140960795 + 5327414 * 2 ^ 59
def prefixEnd_5327414 : Nat := 4983230072969 + 3 ^ 40 * 5327414 * 2
def baseEnd_5327414 : Nat := 911841342497241567308225

theorem tailTrace_5327414 : CollatzResearch.WordTrace tailWord_5327414 prefixEnd_5327414 911841342497241567308225 := by
  unfold tailWord_5327414
  simp only [CollatzResearch.WordTrace]
  refine ⟨12144171970106025169966331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129537834347797601812974197 12144171970106025169966331)
  ·
    refine ⟨18216257955159037754949497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12144171970106025169966331 18216257955159037754949497)
    ·
      refine ⟨13662193466369278316212123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18216257955159037754949497 13662193466369278316212123)
      ·
        refine ⟨20493290199553917474318185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13662193466369278316212123 20493290199553917474318185)
        ·
          refine ⟨15369967649665438105738639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20493290199553917474318185 15369967649665438105738639)
          ·
            refine ⟨23054951474498157158607959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15369967649665438105738639 23054951474498157158607959)
            ·
              refine ⟨34582427211747235737911939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23054951474498157158607959 34582427211747235737911939)
              ·
                refine ⟨51873640817620853606867909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34582427211747235737911939 51873640817620853606867909)
                ·
                  refine ⟨9726307653303910051287733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51873640817620853606867909 9726307653303910051287733)
                  ·
                    refine ⟨911841342497241567308225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9726307653303910051287733 911841342497241567308225)
                    ·
                      rfl

theorem cell23_5327414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_5327414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327414 prefixEnd_5327414 := by exact prefixLift 5327414
  have htrace : WordTrace (prefixWord ++ tailWord_5327414) baseStart_5327414 baseEnd_5327414 := by
    simpa [prefixWord, tailWord_5327414, baseEnd_5327414] using wordTrace_append hprefix tailTrace_5327414
  have hstable : (prefixWord ++ tailWord_5327414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327414).length < 2 ^ (prefixWord ++ tailWord_5327414).sum := by decide
  have hdescent : baseEnd_5327414 < baseStart_5327414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327440 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 10]
def baseStart_5327440 : Nat := 118140960795 + 5327440 * 2 ^ 59
def prefixEnd_5327440 : Nat := 4983230072969 + 3 ^ 40 * 5327440 * 2
def baseEnd_5327440 : Nat := 303948597554304622244395

theorem tailTrace_5327440 : CollatzResearch.WordTrace tailWord_5327440 prefixEnd_5327440 303948597554304622244395 := by
  unfold tailWord_5327440
  simp only [CollatzResearch.WordTrace]
  refine ⟨97153849909801104579953887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129538466546401472773271849 97153849909801104579953887)
  ·
    refine ⟨145730774864701656869930831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97153849909801104579953887 145730774864701656869930831)
    ·
      refine ⟨218596162297052485304896247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145730774864701656869930831 218596162297052485304896247)
      ·
        refine ⟨327894243445578727957344371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218596162297052485304896247 327894243445578727957344371)
        ·
          refine ⟨491841365168368091936016557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327894243445578727957344371 491841365168368091936016557)
          ·
            refine ⟨184440511938138034476006209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 491841365168368091936016557 184440511938138034476006209)
            ·
              refine ⟨138330383953603525857004657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184440511938138034476006209 138330383953603525857004657)
              ·
                refine ⟨103747787965202644392753493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138330383953603525857004657 103747787965202644392753493)
                ·
                  refine ⟨303948597554304622244395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 103747787965202644392753493 303948597554304622244395)
                  ·
                    rfl

theorem cell23_5327440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 10].length) (baseStart_5327440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327440 prefixEnd_5327440 := by exact prefixLift 5327440
  have htrace : WordTrace (prefixWord ++ tailWord_5327440) baseStart_5327440 baseEnd_5327440 := by
    simpa [prefixWord, tailWord_5327440, baseEnd_5327440] using wordTrace_append hprefix tailTrace_5327440
  have hstable : (prefixWord ++ tailWord_5327440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327440).length < 2 ^ (prefixWord ++ tailWord_5327440).sum := by decide
  have hdescent : baseEnd_5327440 < baseStart_5327440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327521 : List Nat := [1, 2, 3, 3, 3, 1, 1, 3, 1, 5]
def baseStart_5327521 : Nat := 118140960795 + 5327521 * 2 ^ 59
def prefixEnd_5327521 : Nat := 4983230072969 + 3 ^ 40 * 5327521 * 2
def baseEnd_5327521 : Nat := 911859656640585261095561

theorem tailTrace_5327521 : CollatzResearch.WordTrace tailWord_5327521 prefixEnd_5327521 911859656640585261095561 := by
  unfold tailWord_5327521
  simp only [CollatzResearch.WordTrace]
  refine ⟨194310654132308759993606417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129540436088205839995737611 194310654132308759993606417)
  ·
    refine ⟨145732990599231569995204813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194310654132308759993606417 145732990599231569995204813)
    ·
      refine ⟨54649871474711838748201805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145732990599231569995204813 54649871474711838748201805)
      ·
        refine ⟨20493701803016939530575677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54649871474711838748201805 20493701803016939530575677)
        ·
          refine ⟨7685138176131352323965879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20493701803016939530575677 7685138176131352323965879)
          ·
            refine ⟨11527707264197028485948819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7685138176131352323965879 11527707264197028485948819)
            ·
              refine ⟨17291560896295542728923229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11527707264197028485948819 17291560896295542728923229)
              ·
                refine ⟨6484335336110828523346211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17291560896295542728923229 6484335336110828523346211)
                ·
                  refine ⟨9726503004166242785019317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6484335336110828523346211 9726503004166242785019317)
                  ·
                    refine ⟨911859656640585261095561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9726503004166242785019317 911859656640585261095561)
                    ·
                      rfl

theorem cell23_5327521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_5327521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327521 prefixEnd_5327521 := by exact prefixLift 5327521
  have htrace : WordTrace (prefixWord ++ tailWord_5327521) baseStart_5327521 baseEnd_5327521 := by
    simpa [prefixWord, tailWord_5327521, baseEnd_5327521] using wordTrace_append hprefix tailTrace_5327521
  have hstable : (prefixWord ++ tailWord_5327521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327521).length < 2 ^ (prefixWord ++ tailWord_5327521).sum := by decide
  have hdescent : baseEnd_5327521 < baseStart_5327521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327564 : List Nat := [2, 2, 1, 5, 1, 2, 1, 9]
def baseStart_5327564 : Nat := 118140960795 + 5327564 * 2 ^ 59
def prefixEnd_5327564 : Nat := 4983230072969 + 3 ^ 40 * 5327564 * 2
def baseEnd_5327564 : Nat := 101318557392218485742555

theorem tailTrace_5327564 : CollatzResearch.WordTrace tailWord_5327564 prefixEnd_5327564 101318557392218485742555 := by
  unfold tailWord_5327564
  simp only [CollatzResearch.WordTrace]
  refine ⟨97156111235576489168710873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129541481647435318891614497 97156111235576489168710873)
  ·
    refine ⟨72867083426682366876533155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97156111235576489168710873 72867083426682366876533155)
    ·
      refine ⟨109300625140023550314799733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72867083426682366876533155 109300625140023550314799733)
      ·
        refine ⟨10246933606877207842012475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109300625140023550314799733 10246933606877207842012475)
        ·
          refine ⟨15370400410315811763018713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10246933606877207842012475 15370400410315811763018713)
          ·
            refine ⟨11527800307736858822264035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15370400410315811763018713 11527800307736858822264035)
            ·
              refine ⟨17291700461605288233396053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11527800307736858822264035 17291700461605288233396053)
              ·
                refine ⟨101318557392218485742555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17291700461605288233396053 101318557392218485742555)
                ·
                  rfl

theorem cell23_5327564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 9].length) (baseStart_5327564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327564 prefixEnd_5327564 := by exact prefixLift 5327564
  have htrace : WordTrace (prefixWord ++ tailWord_5327564) baseStart_5327564 baseEnd_5327564 := by
    simpa [prefixWord, tailWord_5327564, baseEnd_5327564] using wordTrace_append hprefix tailTrace_5327564
  have hstable : (prefixWord ++ tailWord_5327564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327564).length < 2 ^ (prefixWord ++ tailWord_5327564).sum := by decide
  have hdescent : baseEnd_5327564 < baseStart_5327564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327575 : List Nat := [1, 1, 3, 2, 1, 4, 3, 3, 1, 2, 2]
def baseStart_5327575 : Nat := 118140960795 + 5327575 * 2 ^ 59
def prefixEnd_5327575 : Nat := 4983230072969 + 3 ^ 40 * 5327575 * 2
def baseEnd_5327575 : Nat := 2735606697877098572011435

theorem tailTrace_5327575 : CollatzResearch.WordTrace tailWord_5327575 prefixEnd_5327575 2735606697877098572011435 := by
  unfold tailWord_5327575
  simp only [CollatzResearch.WordTrace]
  refine ⟨194312623674113127216072179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129541749116075418144048119 194312623674113127216072179)
  ·
    refine ⟨291468935511169690824108269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194312623674113127216072179 291468935511169690824108269)
    ·
      refine ⟨109300850816688634059040601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291468935511169690824108269 109300850816688634059040601)
      ·
        refine ⟨81975638112516475544280451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109300850816688634059040601 81975638112516475544280451)
        ·
          refine ⟨122963457168774713316420677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81975638112516475544280451 122963457168774713316420677)
          ·
            refine ⟨23055648219145258746828877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122963457168774713316420677 23055648219145258746828877)
            ·
              refine ⟨8645868082179472030060829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23055648219145258746828877 8645868082179472030060829)
              ·
                refine ⟨3242200530817302011272811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8645868082179472030060829 3242200530817302011272811)
                ·
                  refine ⟨4863300796225953016909217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3242200530817302011272811 4863300796225953016909217)
                  ·
                    refine ⟨3647475597169464762681913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4863300796225953016909217 3647475597169464762681913)
                    ·
                      refine ⟨2735606697877098572011435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3647475597169464762681913 2735606697877098572011435)
                      ·
                        rfl

theorem cell23_5327575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_5327575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327575 prefixEnd_5327575 := by exact prefixLift 5327575
  have htrace : WordTrace (prefixWord ++ tailWord_5327575) baseStart_5327575 baseEnd_5327575 := by
    simpa [prefixWord, tailWord_5327575, baseEnd_5327575] using wordTrace_append hprefix tailTrace_5327575
  have hstable : (prefixWord ++ tailWord_5327575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327575).length < 2 ^ (prefixWord ++ tailWord_5327575).sum := by decide
  have hdescent : baseEnd_5327575 < baseStart_5327575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327592 : List Nat := [2, 1, 4, 1, 5, 1, 1, 1, 3, 2, 2]
def baseStart_5327592 : Nat := 118140960795 + 5327592 * 2 ^ 59
def prefixEnd_5327592 : Nat := 4983230072969 + 3 ^ 40 * 5327592 * 2
def baseEnd_5327592 : Nat := 2735615427048225005498857

theorem tailTrace_5327592 : CollatzResearch.WordTrace tailWord_5327592 prefixEnd_5327592 2735615427048225005498857 := by
  unfold tailWord_5327592
  simp only [CollatzResearch.WordTrace]
  refine ⟨97156621857525769559720515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129542162476701026079627353 97156621857525769559720515)
  ·
    refine ⟨145734932786288654339580773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97156621857525769559720515 145734932786288654339580773)
    ·
      refine ⟨27325299897429122688671395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145734932786288654339580773 27325299897429122688671395)
      ·
        refine ⟨40987949846143684033007093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27325299897429122688671395 40987949846143684033007093)
        ·
          refine ⟨3842620298075970378094415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40987949846143684033007093 3842620298075970378094415)
          ·
            refine ⟨5763930447113955567141623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3842620298075970378094415 5763930447113955567141623)
            ·
              refine ⟨8645895670670933350712435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5763930447113955567141623 8645895670670933350712435)
              ·
                refine ⟨12968843506006400026068653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8645895670670933350712435 12968843506006400026068653)
                ·
                  refine ⟨4863316314752400009775745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12968843506006400026068653 4863316314752400009775745)
                  ·
                    refine ⟨3647487236064300007331809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4863316314752400009775745 3647487236064300007331809)
                    ·
                      refine ⟨2735615427048225005498857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3647487236064300007331809 2735615427048225005498857)
                      ·
                        rfl

theorem cell23_5327592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_5327592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327592 prefixEnd_5327592 := by exact prefixLift 5327592
  have htrace : WordTrace (prefixWord ++ tailWord_5327592) baseStart_5327592 baseEnd_5327592 := by
    simpa [prefixWord, tailWord_5327592, baseEnd_5327592] using wordTrace_append hprefix tailTrace_5327592
  have hstable : (prefixWord ++ tailWord_5327592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327592).length < 2 ^ (prefixWord ++ tailWord_5327592).sum := by decide
  have hdescent : baseEnd_5327592 < baseStart_5327592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327601 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2]
def baseStart_5327601 : Nat := 118140960795 + 5327601 * 2 ^ 59
def prefixEnd_5327601 : Nat := 4983230072969 + 3 ^ 40 * 5327601 * 2
def baseEnd_5327601 : Nat := 2735620048374115470286315

theorem tailTrace_5327601 : CollatzResearch.WordTrace tailWord_5327601 prefixEnd_5327601 2735620048374115470286315 := by
  unfold tailWord_5327601
  simp only [CollatzResearch.WordTrace]
  refine ⟨194313571972018933656518657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129542381314679289104345771 194313571972018933656518657)
  ·
    refine ⟨145735178979014200242388993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194313571972018933656518657 145735178979014200242388993)
    ·
      refine ⟨109301384234260650181791745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145735178979014200242388993 109301384234260650181791745)
      ·
        refine ⟨81976038175695487636343809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109301384234260650181791745 81976038175695487636343809)
        ·
          refine ⟨61482028631771615727257857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81976038175695487636343809 61482028631771615727257857)
          ·
            refine ⟨46111521473828711795443393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61482028631771615727257857 46111521473828711795443393)
            ·
              refine ⟨34583641105371533846582545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46111521473828711795443393 34583641105371533846582545)
              ·
                refine ⟨25937730829028650384936909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34583641105371533846582545 25937730829028650384936909)
                ·
                  refine ⟨9726649060885743894351341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25937730829028650384936909 9726649060885743894351341)
                  ·
                    refine ⟨3647493397832153960381753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9726649060885743894351341 3647493397832153960381753)
                    ·
                      refine ⟨2735620048374115470286315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3647493397832153960381753 2735620048374115470286315)
                      ·
                        rfl

theorem cell23_5327601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_5327601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327601 prefixEnd_5327601 := by exact prefixLift 5327601
  have htrace : WordTrace (prefixWord ++ tailWord_5327601) baseStart_5327601 baseEnd_5327601 := by
    simpa [prefixWord, tailWord_5327601, baseEnd_5327601] using wordTrace_append hprefix tailTrace_5327601
  have hstable : (prefixWord ++ tailWord_5327601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327601).length < 2 ^ (prefixWord ++ tailWord_5327601).sum := by decide
  have hdescent : baseEnd_5327601 < baseStart_5327601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327607 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 1, 8]
def baseStart_5327607 : Nat := 118140960795 + 5327607 * 2 ^ 59
def prefixEnd_5327607 : Nat := 4983230072969 + 3 ^ 40 * 5327607 * 2
def baseEnd_5327607 : Nat := 911874376419347482270429

theorem tailTrace_5327607 : CollatzResearch.WordTrace tailWord_5327607 prefixEnd_5327607 911874376419347482270429 := by
  unfold tailWord_5327607
  simp only [CollatzResearch.WordTrace]
  refine ⟨194313790809997196681237075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129542527206664797787491383 194313790809997196681237075)
  ·
    refine ⟨291470686214995795021855613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194313790809997196681237075 291470686214995795021855613)
    ·
      refine ⟨109301507330623423133195855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291470686214995795021855613 109301507330623423133195855)
      ·
        refine ⟨163952260995935134699793783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109301507330623423133195855 163952260995935134699793783)
        ·
          refine ⟨245928391493902702049690675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163952260995935134699793783 245928391493902702049690675)
          ·
            refine ⟨368892587240854053074536013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245928391493902702049690675 368892587240854053074536013)
            ·
              refine ⟨138334720215320269902951005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 368892587240854053074536013 138334720215320269902951005)
              ·
                refine ⟨51875520080745101213606627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138334720215320269902951005 51875520080745101213606627)
                ·
                  refine ⟨77813280121117651820409941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51875520080745101213606627 77813280121117651820409941)
                  ·
                    refine ⟨911874376419347482270429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77813280121117651820409941 911874376419347482270429)
                    ·
                      rfl

theorem cell23_5327607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_5327607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327607 prefixEnd_5327607 := by exact prefixLift 5327607
  have htrace : WordTrace (prefixWord ++ tailWord_5327607) baseStart_5327607 baseEnd_5327607 := by
    simpa [prefixWord, tailWord_5327607, baseEnd_5327607] using wordTrace_append hprefix tailTrace_5327607
  have hstable : (prefixWord ++ tailWord_5327607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327607).length < 2 ^ (prefixWord ++ tailWord_5327607).sum := by decide
  have hdescent : baseEnd_5327607 < baseStart_5327607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327631 : List Nat := [1, 1, 2, 1, 1, 1, 7, 2, 1, 4, 2]
def baseStart_5327631 : Nat := 118140960795 + 5327631 * 2 ^ 59
def prefixEnd_5327631 : Nat := 4983230072969 + 3 ^ 40 * 5327631 * 2
def baseEnd_5327631 : Nat := 2735635452793750352911177

theorem tailTrace_5327631 : CollatzResearch.WordTrace tailWord_5327631 prefixEnd_5327631 2735635452793750352911177 := by
  unfold tailWord_5327631
  simp only [CollatzResearch.WordTrace]
  refine ⟨194314666161910248780110747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129543110774606832520073831 194314666161910248780110747)
  ·
    refine ⟨291471999242865373170166121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194314666161910248780110747 291471999242865373170166121)
    ·
      refine ⟨218603999432149029877624591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291471999242865373170166121 218603999432149029877624591)
      ·
        refine ⟨327905999148223544816436887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218603999432149029877624591 327905999148223544816436887)
        ·
          refine ⟨491858998722335317224655331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327905999148223544816436887 491858998722335317224655331)
          ·
            refine ⟨737788498083502975836982997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491858998722335317224655331 737788498083502975836982997)
            ·
              refine ⟨17291917923832100996179289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 737788498083502975836982997 17291917923832100996179289)
              ·
                refine ⟨12968938442874075747134467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17291917923832100996179289 12968938442874075747134467)
                ·
                  refine ⟨19453407664311113620701701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12968938442874075747134467 19453407664311113620701701)
                  ·
                    refine ⟨3647513937058333803881569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19453407664311113620701701 3647513937058333803881569)
                    ·
                      refine ⟨2735635452793750352911177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3647513937058333803881569 2735635452793750352911177)
                      ·
                        rfl

theorem cell23_5327631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 4, 2].length) (baseStart_5327631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327631 prefixEnd_5327631 := by exact prefixLift 5327631
  have htrace : WordTrace (prefixWord ++ tailWord_5327631) baseStart_5327631 baseEnd_5327631 := by
    simpa [prefixWord, tailWord_5327631, baseEnd_5327631] using wordTrace_append hprefix tailTrace_5327631
  have hstable : (prefixWord ++ tailWord_5327631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327631).length < 2 ^ (prefixWord ++ tailWord_5327631).sum := by decide
  have hdescent : baseEnd_5327631 < baseStart_5327631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327658 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 2, 6]
def baseStart_5327658 : Nat := 118140960795 + 5327658 * 2 ^ 59
def prefixEnd_5327658 : Nat := 4983230072969 + 3 ^ 40 * 5327658 * 2
def baseEnd_5327658 : Nat := 911883105590473915757851

theorem tailTrace_5327658 : CollatzResearch.WordTrace tailWord_5327658 prefixEnd_5327658 911883105590473915757851 := by
  unfold tailWord_5327658
  simp only [CollatzResearch.WordTrace]
  refine ⟨48578912733203108097835907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129543767288541621594229085 48578912733203108097835907)
  ·
    refine ⟨72868369099804662146753861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48578912733203108097835907 72868369099804662146753861)
    ·
      refine ⟨13662819206213374152516349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72868369099804662146753861 13662819206213374152516349)
      ·
        refine ⟨5123557202330015307193631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13662819206213374152516349 5123557202330015307193631)
        ·
          refine ⟨7685335803495022960790447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5123557202330015307193631 7685335803495022960790447)
          ·
            refine ⟨11528003705242534441185671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7685335803495022960790447 11528003705242534441185671)
            ·
              refine ⟨17292005557863801661778507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11528003705242534441185671 17292005557863801661778507)
              ·
                refine ⟨25938008336795702492667761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17292005557863801661778507 25938008336795702492667761)
                ·
                  refine ⟨19453506252596776869500821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25938008336795702492667761 19453506252596776869500821)
                  ·
                    refine ⟨911883105590473915757851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19453506252596776869500821 911883105590473915757851)
                    ·
                      rfl

theorem cell23_5327658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_5327658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327658 prefixEnd_5327658 := by exact prefixLift 5327658
  have htrace : WordTrace (prefixWord ++ tailWord_5327658) baseStart_5327658 baseEnd_5327658 := by
    simpa [prefixWord, tailWord_5327658, baseEnd_5327658] using wordTrace_append hprefix tailTrace_5327658
  have hstable : (prefixWord ++ tailWord_5327658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327658).length < 2 ^ (prefixWord ++ tailWord_5327658).sum := by decide
  have hdescent : baseEnd_5327658 < baseStart_5327658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327686 : List Nat := [6, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_5327686 : Nat := 118140960795 + 5327686 * 2 ^ 59
def prefixEnd_5327686 : Nat := 4983230072969 + 3 ^ 40 * 5327686 * 2
def baseEnd_5327686 : Nat := 2735663694229747637723425

theorem tailTrace_5327686 : CollatzResearch.WordTrace tailWord_5327686 prefixEnd_5327686 2735663694229747637723425 := by
  unfold tailWord_5327686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6072396005522218536667591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 129544448117807328782241941 6072396005522218536667591)
  ·
    refine ⟨9108594008283327805001387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6072396005522218536667591 9108594008283327805001387)
    ·
      refine ⟨13662891012424991707502081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9108594008283327805001387 13662891012424991707502081)
      ·
        refine ⟨10247168259318743780626561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13662891012424991707502081 10247168259318743780626561)
        ·
          refine ⟨7685376194489057835469921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10247168259318743780626561 7685376194489057835469921)
          ·
            refine ⟨5764032145866793376602441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7685376194489057835469921 5764032145866793376602441)
            ·
              refine ⟨4323024109400095032451831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5764032145866793376602441 4323024109400095032451831)
              ·
                refine ⟨6484536164100142548677747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4323024109400095032451831 6484536164100142548677747)
                ·
                  refine ⟨9726804246150213823016621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6484536164100142548677747 9726804246150213823016621)
                  ·
                    refine ⟨3647551592306330183631233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9726804246150213823016621 3647551592306330183631233)
                    ·
                      refine ⟨2735663694229747637723425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3647551592306330183631233 2735663694229747637723425)
                      ·
                        rfl

theorem cell23_5327686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_5327686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327686 prefixEnd_5327686 := by exact prefixLift 5327686
  have htrace : WordTrace (prefixWord ++ tailWord_5327686) baseStart_5327686 baseEnd_5327686 := by
    simpa [prefixWord, tailWord_5327686, baseEnd_5327686] using wordTrace_append hprefix tailTrace_5327686
  have hstable : (prefixWord ++ tailWord_5327686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327686).length < 2 ^ (prefixWord ++ tailWord_5327686).sum := by decide
  have hdescent : baseEnd_5327686 < baseStart_5327686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327694 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_5327694 : Nat := 118140960795 + 5327694 * 2 ^ 59
def prefixEnd_5327694 : Nat := 4983230072969 + 3 ^ 40 * 5327694 * 2
def baseEnd_5327694 : Nat := 2735667802074983606423387

theorem tailTrace_5327694 : CollatzResearch.WordTrace tailWord_5327694 prefixEnd_5327694 2735667802074983606423387 := by
  unfold tailWord_5327694
  simp only [CollatzResearch.WordTrace]
  refine ⟨24289620495085251317456767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129544642640454673693102757 24289620495085251317456767)
  ·
    refine ⟨36434430742627876976185151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24289620495085251317456767 36434430742627876976185151)
    ·
      refine ⟨54651646113941815464277727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36434430742627876976185151 54651646113941815464277727)
      ·
        refine ⟨81977469170912723196416591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54651646113941815464277727 81977469170912723196416591)
        ·
          refine ⟨122966203756369084794624887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81977469170912723196416591 122966203756369084794624887)
          ·
            refine ⟨184449305634553627191937331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122966203756369084794624887 184449305634553627191937331)
            ·
              refine ⟨276673958451830440787905997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184449305634553627191937331 276673958451830440787905997)
              ·
                refine ⟨103752734419436415295464749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276673958451830440787905997 103752734419436415295464749)
                ·
                  refine ⟨38907275407288655735799281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103752734419436415295464749 38907275407288655735799281)
                  ·
                    refine ⟨29180456555466491801849461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38907275407288655735799281 29180456555466491801849461)
                    ·
                      refine ⟨2735667802074983606423387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29180456555466491801849461 2735667802074983606423387)
                      ·
                        rfl

theorem cell23_5327694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_5327694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327694 prefixEnd_5327694 := by exact prefixLift 5327694
  have htrace : WordTrace (prefixWord ++ tailWord_5327694) baseStart_5327694 baseEnd_5327694 := by
    simpa [prefixWord, tailWord_5327694, baseEnd_5327694] using wordTrace_append hprefix tailTrace_5327694
  have hstable : (prefixWord ++ tailWord_5327694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327694).length < 2 ^ (prefixWord ++ tailWord_5327694).sum := by decide
  have hdescent : baseEnd_5327694 < baseStart_5327694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327731 : List Nat := [1, 1, 1, 2, 2, 1, 6, 2, 3, 4]
def baseStart_5327731 : Nat := 118140960795 + 5327731 * 2 ^ 59
def prefixEnd_5327731 : Nat := 4983230072969 + 3 ^ 40 * 5327731 * 2
def baseEnd_5327731 : Nat := 911895600286399987220239

theorem tailTrace_5327731 : CollatzResearch.WordTrace tailWord_5327731 prefixEnd_5327731 911895600286399987220239 := by
  unfold tailWord_5327731
  simp only [CollatzResearch.WordTrace]
  refine ⟨194318313461547965858751047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129545542307698643905834031 194318313461547965858751047)
  ·
    refine ⟨291477470192321948788126571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194318313461547965858751047 291477470192321948788126571)
    ·
      refine ⟨437216205288482923182189857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291477470192321948788126571 437216205288482923182189857)
      ·
        refine ⟨327912153966362192386642393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437216205288482923182189857 327912153966362192386642393)
        ·
          refine ⟨245934115474771644289981795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327912153966362192386642393 245934115474771644289981795)
          ·
            refine ⟨368901173212157466434972693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245934115474771644289981795 368901173212157466434972693)
            ·
              refine ⟨17292242494319881239139345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 368901173212157466434972693 17292242494319881239139345)
              ·
                refine ⟨12969181870739910929354509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17292242494319881239139345 12969181870739910929354509)
                ·
                  refine ⟨4863443201527466598507941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12969181870739910929354509 4863443201527466598507941)
                  ·
                    refine ⟨911895600286399987220239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4863443201527466598507941 911895600286399987220239)
                    ·
                      rfl

theorem cell23_5327731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 4].length) (baseStart_5327731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327731 prefixEnd_5327731 := by exact prefixLift 5327731
  have htrace : WordTrace (prefixWord ++ tailWord_5327731) baseStart_5327731 baseEnd_5327731 := by
    simpa [prefixWord, tailWord_5327731, baseEnd_5327731] using wordTrace_append hprefix tailTrace_5327731
  have hstable : (prefixWord ++ tailWord_5327731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327731).length < 2 ^ (prefixWord ++ tailWord_5327731).sum := by decide
  have hdescent : baseEnd_5327731 < baseStart_5327731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327741 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 1, 4, 3]
def baseStart_5327741 : Nat := 118140960795 + 5327741 * 2 ^ 59
def prefixEnd_5327741 : Nat := 4983230072969 + 3 ^ 40 * 5327741 * 2
def baseEnd_5327741 : Nat := 2735691935665744922535671

theorem tailTrace_5327741 : CollatzResearch.WordTrace tailWord_5327741 prefixEnd_5327741 2735691935665744922535671 := by
  unfold tailWord_5327741
  simp only [CollatzResearch.WordTrace]
  refine ⟨194318678191511737566615077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129545785461007825044410051 194318678191511737566615077)
  ·
    refine ⟨36434752160908450793740327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194318678191511737566615077 36434752160908450793740327)
    ·
      refine ⟨54652128241362676190610491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36434752160908450793740327 54652128241362676190610491)
      ·
        refine ⟨81978192362044014285915737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54652128241362676190610491 81978192362044014285915737)
        ·
          refine ⟨61483644271533010714436803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81978192362044014285915737 61483644271533010714436803)
          ·
            refine ⟨92225466407299516071655205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61483644271533010714436803 92225466407299516071655205)
            ·
              refine ⟨17292274951368659263435351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92225466407299516071655205 17292274951368659263435351)
              ·
                refine ⟨25938412427052988895153027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17292274951368659263435351 25938412427052988895153027)
                ·
                  refine ⟨38907618640579483342729541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25938412427052988895153027 38907618640579483342729541)
                  ·
                    refine ⟨7295178495108653126761789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38907618640579483342729541 7295178495108653126761789)
                    ·
                      refine ⟨2735691935665744922535671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7295178495108653126761789 2735691935665744922535671)
                      ·
                        rfl

theorem cell23_5327741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_5327741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327741 prefixEnd_5327741 := by exact prefixLift 5327741
  have htrace : WordTrace (prefixWord ++ tailWord_5327741) baseStart_5327741 baseEnd_5327741 := by
    simpa [prefixWord, tailWord_5327741, baseEnd_5327741] using wordTrace_append hprefix tailTrace_5327741
  have hstable : (prefixWord ++ tailWord_5327741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327741).length < 2 ^ (prefixWord ++ tailWord_5327741).sum := by decide
  have hdescent : baseEnd_5327741 < baseStart_5327741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327778 : List Nat := [3, 3, 1, 2, 2, 2, 1, 3, 6]
def baseStart_5327778 : Nat := 118140960795 + 5327778 * 2 ^ 59
def prefixEnd_5327778 : Nat := 4983230072969 + 3 ^ 40 * 5327778 * 2
def baseEnd_5327778 : Nat := 303967881605551253085889

theorem tailTrace_5327778 : CollatzResearch.WordTrace tailWord_5327778 prefixEnd_5327778 303967881605551253085889 := by
  unfold tailWord_5327778
  simp only [CollatzResearch.WordTrace]
  refine ⟨48580006923094423221427997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129546685128251795257141325 48580006923094423221427997)
  ·
    refine ⟨18217502596160408708035499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48580006923094423221427997 18217502596160408708035499)
    ·
      refine ⟨27326253894240613062053249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18217502596160408708035499 27326253894240613062053249)
      ·
        refine ⟨20494690420680459796539937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27326253894240613062053249 20494690420680459796539937)
        ·
          refine ⟨15371017815510344847404953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20494690420680459796539937 15371017815510344847404953)
          ·
            refine ⟨11528263361632758635553715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15371017815510344847404953 11528263361632758635553715)
            ·
              refine ⟨17292395042449137953330573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11528263361632758635553715 17292395042449137953330573)
              ·
                refine ⟨6484648140918426732498965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17292395042449137953330573 6484648140918426732498965)
                ·
                  refine ⟨303967881605551253085889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6484648140918426732498965 303967881605551253085889)
                  ·
                    rfl

theorem cell23_5327778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_5327778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327778 prefixEnd_5327778 := by exact prefixLift 5327778
  have htrace : WordTrace (prefixWord ++ tailWord_5327778) baseStart_5327778 baseEnd_5327778 := by
    simpa [prefixWord, tailWord_5327778, baseEnd_5327778] using wordTrace_append hprefix tailTrace_5327778
  have hstable : (prefixWord ++ tailWord_5327778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327778).length < 2 ^ (prefixWord ++ tailWord_5327778).sum := by decide
  have hdescent : baseEnd_5327778 < baseStart_5327778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327791 : List Nat := [1, 1, 2, 1, 2, 2, 2, 6, 1, 5]
def baseStart_5327791 : Nat := 118140960795 + 5327791 * 2 ^ 59
def prefixEnd_5327791 : Nat := 4983230072969 + 3 ^ 40 * 5327791 * 2
def baseEnd_5327791 : Nat := 911905869899489908970147

theorem tailTrace_5327791 : CollatzResearch.WordTrace tailWord_5327791 prefixEnd_5327791 911905869899489908970147 := by
  unfold tailWord_5327791
  simp only [CollatzResearch.WordTrace]
  refine ⟨194320501841330596105935227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129547001227553730737290151 194320501841330596105935227)
  ·
    refine ⟨291480752761995894158902841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194320501841330596105935227 291480752761995894158902841)
    ·
      refine ⟨218610564571496920619177131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291480752761995894158902841 218610564571496920619177131)
      ·
        refine ⟨327915846857245380928765697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218610564571496920619177131 327915846857245380928765697)
        ·
          refine ⟨245936885142934035696574273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327915846857245380928765697 245936885142934035696574273)
          ·
            refine ⟨184452663857200526772430705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245936885142934035696574273 184452663857200526772430705)
            ·
              refine ⟨138339497892900395079323029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184452663857200526772430705 138339497892900395079323029)
              ·
                refine ⟨6484663963729706019343267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 138339497892900395079323029 6484663963729706019343267)
                ·
                  refine ⟨9726995945594559029014901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6484663963729706019343267 9726995945594559029014901)
                  ·
                    refine ⟨911905869899489908970147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9726995945594559029014901 911905869899489908970147)
                    ·
                      rfl

theorem cell23_5327791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 5].length) (baseStart_5327791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327791 prefixEnd_5327791 := by exact prefixLift 5327791
  have htrace : WordTrace (prefixWord ++ tailWord_5327791) baseStart_5327791 baseEnd_5327791 := by
    simpa [prefixWord, tailWord_5327791, baseEnd_5327791] using wordTrace_append hprefix tailTrace_5327791
  have hstable : (prefixWord ++ tailWord_5327791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327791).length < 2 ^ (prefixWord ++ tailWord_5327791).sum := by decide
  have hdescent : baseEnd_5327791 < baseStart_5327791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327822 : List Nat := [4, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3]
def baseStart_5327822 : Nat := 118140960795 + 5327822 * 2 ^ 59
def prefixEnd_5327822 : Nat := 4983230072969 + 3 ^ 40 * 5327822 * 2
def baseEnd_5327822 : Nat := 2735733527598759105622799

theorem tailTrace_5327822 : CollatzResearch.WordTrace tailWord_5327822 prefixEnd_5327822 2735733527598759105622799 := by
  unfold tailWord_5327822
  simp only [CollatzResearch.WordTrace]
  refine ⟨24290204063027286050039215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129547755002812192266875813 24290204063027286050039215)
  ·
    refine ⟨36435306094540929075058823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24290204063027286050039215 36435306094540929075058823)
    ·
      refine ⟨54652959141811393612588235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36435306094540929075058823 54652959141811393612588235)
      ·
        refine ⟨81979438712717090418882353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54652959141811393612588235 81979438712717090418882353)
        ·
          refine ⟨61484579034537817814161765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81979438712717090418882353 61484579034537817814161765)
          ·
            refine ⟨11528358568975840840155331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61484579034537817814161765 11528358568975840840155331)
            ·
              refine ⟨17292537853463761260232997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11528358568975840840155331 17292537853463761260232997)
              ·
                refine ⟨3242350847524455236293687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17292537853463761260232997 3242350847524455236293687)
                ·
                  refine ⟨4863526271286682854440531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3242350847524455236293687 4863526271286682854440531)
                  ·
                    refine ⟨7295289406930024281660797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4863526271286682854440531 7295289406930024281660797)
                    ·
                      refine ⟨2735733527598759105622799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7295289406930024281660797 2735733527598759105622799)
                      ·
                        rfl

theorem cell23_5327822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_5327822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327822 prefixEnd_5327822 := by exact prefixLift 5327822
  have htrace : WordTrace (prefixWord ++ tailWord_5327822) baseStart_5327822 baseEnd_5327822 := by
    simpa [prefixWord, tailWord_5327822, baseEnd_5327822] using wordTrace_append hprefix tailTrace_5327822
  have hstable : (prefixWord ++ tailWord_5327822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327822).length < 2 ^ (prefixWord ++ tailWord_5327822).sum := by decide
  have hdescent : baseEnd_5327822 < baseStart_5327822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327828 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_5327828 : Nat := 118140960795 + 5327828 * 2 ^ 59
def prefixEnd_5327828 : Nat := 4983230072969 + 3 ^ 40 * 5327828 * 2
def baseEnd_5327828 : Nat := 2735736608482686082147771

theorem tailTrace_5327828 : CollatzResearch.WordTrace tailWord_5327828 prefixEnd_5327828 2735736608482686082147771 := by
  unfold tailWord_5327828
  simp only [CollatzResearch.WordTrace]
  refine ⟨97160925671098275712516069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129547900894797700950021425 97160925671098275712516069)
  ·
    refine ⟨18217673563330926696096763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97160925671098275712516069 18217673563330926696096763)
    ·
      refine ⟨27326510344996390044145145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18217673563330926696096763 27326510344996390044145145)
      ·
        refine ⟨20494882758747292533108859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27326510344996390044145145 20494882758747292533108859)
        ·
          refine ⟨30742324138120938799663289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20494882758747292533108859 30742324138120938799663289)
          ·
            refine ⟨23056743103590704099747467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30742324138120938799663289 23056743103590704099747467)
            ·
              refine ⟨34585114655386056149621201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23056743103590704099747467 34585114655386056149621201)
              ·
                refine ⟨25938835991539542112215901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34585114655386056149621201 25938835991539542112215901)
                ·
                  refine ⟨9727063496827328292080963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25938835991539542112215901 9727063496827328292080963)
                  ·
                    refine ⟨14590595245240992438121445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9727063496827328292080963 14590595245240992438121445)
                    ·
                      refine ⟨2735736608482686082147771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14590595245240992438121445 2735736608482686082147771)
                      ·
                        rfl

theorem cell23_5327828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_5327828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327828 prefixEnd_5327828 := by exact prefixLift 5327828
  have htrace : WordTrace (prefixWord ++ tailWord_5327828) baseStart_5327828 baseEnd_5327828 := by
    simpa [prefixWord, tailWord_5327828, baseEnd_5327828] using wordTrace_append hprefix tailTrace_5327828
  have hstable : (prefixWord ++ tailWord_5327828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327828).length < 2 ^ (prefixWord ++ tailWord_5327828).sum := by decide
  have hdescent : baseEnd_5327828 < baseStart_5327828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327848 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_5327848 : Nat := 118140960795 + 5327848 * 2 ^ 59
def prefixEnd_5327848 : Nat := 4983230072969 + 3 ^ 40 * 5327848 * 2
def baseEnd_5327848 : Nat := 2735746878095776003897679

theorem tailTrace_5327848 : CollatzResearch.WordTrace tailWord_5327848 prefixEnd_5327848 2735746878095776003897679 := by
  unfold tailWord_5327848
  simp only [CollatzResearch.WordTrace]
  refine ⟨97161290401062047420380099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129548387201416063227173465 97161290401062047420380099)
  ·
    refine ⟨145741935601593071130570149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97161290401062047420380099 145741935601593071130570149)
    ·
      refine ⟨27326612925298700836981903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145741935601593071130570149 27326612925298700836981903)
      ·
        refine ⟨40989919387948051255472855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27326612925298700836981903 40989919387948051255472855)
        ·
          refine ⟨61484879081922076883209283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40989919387948051255472855 61484879081922076883209283)
          ·
            refine ⟨92227318622883115324813925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61484879081922076883209283 92227318622883115324813925)
            ·
              refine ⟨17292622241790584123402611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92227318622883115324813925 17292622241790584123402611)
              ·
                refine ⟨25938933362685876185103917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17292622241790584123402611 25938933362685876185103917)
                ·
                  refine ⟨9727100011007203569413969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25938933362685876185103917 9727100011007203569413969)
                  ·
                    refine ⟨7295325008255402677060477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9727100011007203569413969 7295325008255402677060477)
                    ·
                      refine ⟨2735746878095776003897679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7295325008255402677060477 2735746878095776003897679)
                      ·
                        rfl

theorem cell23_5327848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_5327848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327848 prefixEnd_5327848 := by exact prefixLift 5327848
  have htrace : WordTrace (prefixWord ++ tailWord_5327848) baseStart_5327848 baseEnd_5327848 := by
    simpa [prefixWord, tailWord_5327848, baseEnd_5327848] using wordTrace_append hprefix tailTrace_5327848
  have hstable : (prefixWord ++ tailWord_5327848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327848).length < 2 ^ (prefixWord ++ tailWord_5327848).sum := by decide
  have hdescent : baseEnd_5327848 < baseStart_5327848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327862 : List Nat := [5, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4]
def baseStart_5327862 : Nat := 118140960795 + 5327862 * 2 ^ 59
def prefixEnd_5327862 : Nat := 4983230072969 + 3 ^ 40 * 5327862 * 2
def baseEnd_5327862 : Nat := 2735754066824938949122615

theorem tailTrace_5327862 : CollatzResearch.WordTrace tailWord_5327862 prefixEnd_5327862 2735754066824938949122615 := by
  unfold tailWord_5327862
  simp only [CollatzResearch.WordTrace]
  refine ⟨12145193214004585951985615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129548727616048916821179893 12145193214004585951985615)
  ·
    refine ⟨18217789821006878927978423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12145193214004585951985615 18217789821006878927978423)
    ·
      refine ⟨27326684731510318391967635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18217789821006878927978423 27326684731510318391967635)
      ·
        refine ⟨40990027097265477587951453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27326684731510318391967635 40990027097265477587951453)
        ·
          refine ⟨15371260161474554095481795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40990027097265477587951453 15371260161474554095481795)
          ·
            refine ⟨23056890242211831143222693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15371260161474554095481795 23056890242211831143222693)
            ·
              refine ⟨4323166920414718339354255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23056890242211831143222693 4323166920414718339354255)
              ·
                refine ⟨6484750380622077509031383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4323166920414718339354255 6484750380622077509031383)
                ·
                  refine ⟨9727125570933116263547075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6484750380622077509031383 9727125570933116263547075)
                  ·
                    refine ⟨14590688356399674395320613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9727125570933116263547075 14590688356399674395320613)
                    ·
                      refine ⟨2735754066824938949122615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14590688356399674395320613 2735754066824938949122615)
                      ·
                        rfl

theorem cell23_5327862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_5327862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327862 prefixEnd_5327862 := by exact prefixLift 5327862
  have htrace : WordTrace (prefixWord ++ tailWord_5327862) baseStart_5327862 baseEnd_5327862 := by
    simpa [prefixWord, tailWord_5327862, baseEnd_5327862] using wordTrace_append hprefix tailTrace_5327862
  have hstable : (prefixWord ++ tailWord_5327862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327862).length < 2 ^ (prefixWord ++ tailWord_5327862).sum := by decide
  have hdescent : baseEnd_5327862 < baseStart_5327862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327895 : List Nat := [1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 3]
def baseStart_5327895 : Nat := 118140960795 + 5327895 * 2 ^ 59
def prefixEnd_5327895 : Nat := 4983230072969 + 3 ^ 40 * 5327895 * 2
def baseEnd_5327895 : Nat := 2735771011686537320009963

theorem tailTrace_5327895 : CollatzResearch.WordTrace tailWord_5327895 prefixEnd_5327895 2735771011686537320009963 := by
  unfold tailWord_5327895
  simp only [CollatzResearch.WordTrace]
  refine ⟨194324295032953821867721139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129549530021969214578480759 194324295032953821867721139)
  ·
    refine ⟨291486442549430732801581709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194324295032953821867721139 291486442549430732801581709)
    ·
      refine ⟨109307415956036524800593141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291486442549430732801581709 109307415956036524800593141)
      ·
        refine ⟨10247570245878424200055607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109307415956036524800593141 10247570245878424200055607)
        ·
          refine ⟨15371355368817636300083411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10247570245878424200055607 15371355368817636300083411)
          ·
            refine ⟨23057033053226454450125117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15371355368817636300083411 23057033053226454450125117)
            ·
              refine ⟨8646387394959920418796919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23057033053226454450125117 8646387394959920418796919)
              ·
                refine ⟨12969581092439880628195379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8646387394959920418796919 12969581092439880628195379)
                ·
                  refine ⟨19454371638659820942293069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12969581092439880628195379 19454371638659820942293069)
                  ·
                    refine ⟨7295389364497432853359901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19454371638659820942293069 7295389364497432853359901)
                    ·
                      refine ⟨2735771011686537320009963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7295389364497432853359901 2735771011686537320009963)
                      ·
                        rfl

theorem cell23_5327895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_5327895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327895 prefixEnd_5327895 := by exact prefixLift 5327895
  have htrace : WordTrace (prefixWord ++ tailWord_5327895) baseStart_5327895 baseEnd_5327895 := by
    simpa [prefixWord, tailWord_5327895, baseEnd_5327895] using wordTrace_append hprefix tailTrace_5327895
  have hstable : (prefixWord ++ tailWord_5327895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327895).length < 2 ^ (prefixWord ++ tailWord_5327895).sum := by decide
  have hdescent : baseEnd_5327895 < baseStart_5327895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5327908 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_5327908 : Nat := 118140960795 + 5327908 * 2 ^ 59
def prefixEnd_5327908 : Nat := 4983230072969 + 3 ^ 40 * 5327908 * 2
def baseEnd_5327908 : Nat := 2735777686935045769147403

theorem tailTrace_5327908 : CollatzResearch.WordTrace tailWord_5327908 prefixEnd_5327908 2735777686935045769147403 := by
  unfold tailWord_5327908
  simp only [CollatzResearch.WordTrace]
  refine ⟨97162384590953362543972189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129549846121271150058629585 97162384590953362543972189)
  ·
    refine ⟨36435894221607510953989571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97162384590953362543972189 36435894221607510953989571)
    ·
      refine ⟨54653841332411266430984357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36435894221607510953989571 54653841332411266430984357)
      ·
        refine ⟨10247595249827112455809567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54653841332411266430984357 10247595249827112455809567)
        ·
          refine ⟨15371392874740668683714351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10247595249827112455809567 15371392874740668683714351)
          ·
            refine ⟨23057089312111003025571527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15371392874740668683714351 23057089312111003025571527)
            ·
              refine ⟨34585633968166504538357291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23057089312111003025571527 34585633968166504538357291)
              ·
                refine ⟨51878450952249756807535937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34585633968166504538357291 51878450952249756807535937)
                ·
                  refine ⟨38908838214187317605651953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51878450952249756807535937 38908838214187317605651953)
                  ·
                    refine ⟨29181628660640488204238965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38908838214187317605651953 29181628660640488204238965)
                    ·
                      refine ⟨2735777686935045769147403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29181628660640488204238965 2735777686935045769147403)
                      ·
                        rfl

theorem cell23_5327908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_5327908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5327908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5327908 prefixEnd_5327908 := by exact prefixLift 5327908
  have htrace : WordTrace (prefixWord ++ tailWord_5327908) baseStart_5327908 baseEnd_5327908 := by
    simpa [prefixWord, tailWord_5327908, baseEnd_5327908] using wordTrace_append hprefix tailTrace_5327908
  have hstable : (prefixWord ++ tailWord_5327908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5327908).length < 2 ^ (prefixWord ++ tailWord_5327908).sum := by decide
  have hdescent : baseEnd_5327908 < baseStart_5327908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5327908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328075 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 5, 1, 3]
def baseStart_5328075 : Nat := 118140960795 + 5328075 * 2 ^ 59
def prefixEnd_5328075 : Nat := 4983230072969 + 3 ^ 40 * 5328075 * 2
def baseEnd_5328075 : Nat := 2735863438204346615759135

theorem tailTrace_5328075 : CollatzResearch.WordTrace tailWord_5328075 prefixEnd_5328075 2735863438204346615759135 := by
  unfold tailWord_5328075
  simp only [CollatzResearch.WordTrace]
  refine ⟨194330860172301712609273679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129553906781534475072849119 194330860172301712609273679)
  ·
    refine ⟨291496290258452568913910519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194330860172301712609273679 291496290258452568913910519)
    ·
      refine ⟨437244435387678853370865779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291496290258452568913910519 437244435387678853370865779)
      ·
        refine ⟨655866653081518280056298669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437244435387678853370865779 655866653081518280056298669)
        ·
          refine ⟨245949994905569355021112001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 655866653081518280056298669 245949994905569355021112001)
          ·
            refine ⟨184462496179177016265834001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245949994905569355021112001 184462496179177016265834001)
            ·
              refine ⟨138346872134382762199375501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184462496179177016265834001 138346872134382762199375501)
              ·
                refine ⟨51880077050393535824765813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138346872134382762199375501 51880077050393535824765813)
                ·
                  refine ⟨4863757223474393983571795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51880077050393535824765813 4863757223474393983571795)
                  ·
                    refine ⟨7295635835211590975357693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4863757223474393983571795 7295635835211590975357693)
                    ·
                      refine ⟨2735863438204346615759135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7295635835211590975357693 2735863438204346615759135)
                      ·
                        rfl

theorem cell23_5328075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 1, 3].length) (baseStart_5328075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328075 prefixEnd_5328075 := by exact prefixLift 5328075
  have htrace : WordTrace (prefixWord ++ tailWord_5328075) baseStart_5328075 baseEnd_5328075 := by
    simpa [prefixWord, tailWord_5328075, baseEnd_5328075] using wordTrace_append hprefix tailTrace_5328075
  have hstable : (prefixWord ++ tailWord_5328075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328075).length < 2 ^ (prefixWord ++ tailWord_5328075).sum := by decide
  have hdescent : baseEnd_5328075 < baseStart_5328075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328095 : List Nat := [1, 1, 2, 3, 2, 1, 4, 3, 1, 5]
def baseStart_5328095 : Nat := 118140960795 + 5328095 * 2 ^ 59
def prefixEnd_5328095 : Nat := 4983230072969 + 3 ^ 40 * 5328095 * 2
def baseEnd_5328095 : Nat := 911957902605812179169681

theorem tailTrace_5328095 : CollatzResearch.WordTrace tailWord_5328095 prefixEnd_5328095 911957902605812179169681 := by
  unfold tailWord_5328095
  simp only [CollatzResearch.WordTrace]
  refine ⟨194331589632229256025001739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129554393088152837350001159 194331589632229256025001739)
  ·
    refine ⟨291497384448343884037502609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194331589632229256025001739 291497384448343884037502609)
    ·
      refine ⟨218623038336257913028126957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291497384448343884037502609 218623038336257913028126957)
      ·
        refine ⟨81983639376096717385547609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218623038336257913028126957 81983639376096717385547609)
        ·
          refine ⟨61487729532072538039160707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81983639376096717385547609 61487729532072538039160707)
          ·
            refine ⟨92231594298108807058741061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61487729532072538039160707 92231594298108807058741061)
            ·
              refine ⟨17293423930895401323513949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92231594298108807058741061 17293423930895401323513949)
              ·
                refine ⟨6485033974085775496317731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17293423930895401323513949 6485033974085775496317731)
                ·
                  refine ⟨9727550961128663244476597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6485033974085775496317731 9727550961128663244476597)
                  ·
                    refine ⟨911957902605812179169681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9727550961128663244476597 911957902605812179169681)
                    ·
                      rfl

theorem cell23_5328095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 5].length) (baseStart_5328095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328095 prefixEnd_5328095 := by exact prefixLift 5328095
  have htrace : WordTrace (prefixWord ++ tailWord_5328095) baseStart_5328095 baseEnd_5328095 := by
    simpa [prefixWord, tailWord_5328095, baseEnd_5328095] using wordTrace_append hprefix tailTrace_5328095
  have hstable : (prefixWord ++ tailWord_5328095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328095).length < 2 ^ (prefixWord ++ tailWord_5328095).sum := by decide
  have hdescent : baseEnd_5328095 < baseStart_5328095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328109 : List Nat := [1, 5, 1, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_5328109 : Nat := 118140960795 + 5328109 * 2 ^ 59
def prefixEnd_5328109 : Nat := 4983230072969 + 3 ^ 40 * 5328109 * 2
def baseEnd_5328109 : Nat := 2735880896546599482733979

theorem tailTrace_5328109 : CollatzResearch.WordTrace tailWord_5328109 prefixEnd_5328109 2735880896546599482733979 := by
  unfold tailWord_5328109
  simp only [CollatzResearch.WordTrace]
  refine ⟨194332100254178536416011381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129554733502785690944007587 194332100254178536416011381)
  ·
    refine ⟨18218634398829237789001067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194332100254178536416011381 18218634398829237789001067)
    ·
      refine ⟨27327951598243856683501601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18218634398829237789001067 27327951598243856683501601)
      ·
        refine ⟨20495963698682892512626201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27327951598243856683501601 20495963698682892512626201)
        ·
          refine ⟨15371972774012169384469651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20495963698682892512626201 15371972774012169384469651)
          ·
            refine ⟨23057959161018254076704477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15371972774012169384469651 23057959161018254076704477)
            ·
              refine ⟨8646734685381845278764179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23057959161018254076704477 8646734685381845278764179)
              ·
                refine ⟨12970102028072767918146269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8646734685381845278764179 12970102028072767918146269)
                ·
                  refine ⟨4863788260527287969304851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12970102028072767918146269 4863788260527287969304851)
                  ·
                    refine ⟨7295682390790931953957277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4863788260527287969304851 7295682390790931953957277)
                    ·
                      refine ⟨2735880896546599482733979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7295682390790931953957277 2735880896546599482733979)
                      ·
                        rfl

theorem cell23_5328109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_5328109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328109 prefixEnd_5328109 := by exact prefixLift 5328109
  have htrace : WordTrace (prefixWord ++ tailWord_5328109) baseStart_5328109 baseEnd_5328109 := by
    simpa [prefixWord, tailWord_5328109, baseEnd_5328109] using wordTrace_append hprefix tailTrace_5328109
  have hstable : (prefixWord ++ tailWord_5328109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328109).length < 2 ^ (prefixWord ++ tailWord_5328109).sum := by decide
  have hdescent : baseEnd_5328109 < baseStart_5328109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328116 : List Nat := [2, 6, 1, 2, 1, 1, 1, 3, 6]
def baseStart_5328116 : Nat := 118140960795 + 5328116 * 2 ^ 59
def prefixEnd_5328116 : Nat := 4983230072969 + 3 ^ 40 * 5328116 * 2
def baseEnd_5328116 : Nat := 303987165656797883927383

theorem tailTrace_5328116 : CollatzResearch.WordTrace tailWord_5328116 prefixEnd_5328116 303987165656797883927383 := by
  unfold tailWord_5328116
  simp only [CollatzResearch.WordTrace]
  refine ⟨97166177782576588305758101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129554903710102117741010801 97166177782576588305758101)
  ·
    refine ⟨4554664583558277576832411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 97166177782576588305758101 4554664583558277576832411)
    ·
      refine ⟨6831996875337416365248617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4554664583558277576832411 6831996875337416365248617)
      ·
        refine ⟨5123997656503062273936463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6831996875337416365248617 5123997656503062273936463)
        ·
          refine ⟨7685996484754593410904695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5123997656503062273936463 7685996484754593410904695)
          ·
            refine ⟨11528994727131890116357043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7685996484754593410904695 11528994727131890116357043)
            ·
              refine ⟨17293492090697835174535565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11528994727131890116357043 17293492090697835174535565)
              ·
                refine ⟨6485059534011688190450837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17293492090697835174535565 6485059534011688190450837)
                ·
                  refine ⟨303987165656797883927383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6485059534011688190450837 303987165656797883927383)
                  ·
                    rfl

theorem cell23_5328116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_5328116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328116 prefixEnd_5328116 := by exact prefixLift 5328116
  have htrace : WordTrace (prefixWord ++ tailWord_5328116) baseStart_5328116 baseEnd_5328116 := by
    simpa [prefixWord, tailWord_5328116, baseEnd_5328116] using wordTrace_append hprefix tailTrace_5328116
  have hstable : (prefixWord ++ tailWord_5328116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328116).length < 2 ^ (prefixWord ++ tailWord_5328116).sum := by decide
  have hdescent : baseEnd_5328116 < baseStart_5328116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328132 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_5328132 : Nat := 118140960795 + 5328132 * 2 ^ 59
def prefixEnd_5328132 : Nat := 4983230072969 + 3 ^ 40 * 5328132 * 2
def baseEnd_5328132 : Nat := 2735892706601652892746373

theorem tailTrace_5328132 : CollatzResearch.WordTrace tailWord_5328132 prefixEnd_5328132 2735892706601652892746373 := by
  unfold tailWord_5328132
  simp only [CollatzResearch.WordTrace]
  refine ⟨97166469566547605672049325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129555292755396807562732433 97166469566547605672049325)
  ·
    refine ⟨36437426087455352127018497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97166469566547605672049325 36437426087455352127018497)
    ·
      refine ⟨27328069565591514095263873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36437426087455352127018497 27328069565591514095263873)
      ·
        refine ⟨20496052174193635571447905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27328069565591514095263873 20496052174193635571447905)
        ·
          refine ⟨15372039130645226678585929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20496052174193635571447905 15372039130645226678585929)
          ·
            refine ⟨11529029347983920008939447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15372039130645226678585929 11529029347983920008939447)
            ·
              refine ⟨17293544021975880013409171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11529029347983920008939447 17293544021975880013409171)
              ·
                refine ⟨25940316032963820020113757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17293544021975880013409171 25940316032963820020113757)
                ·
                  refine ⟨9727618512361432507542659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25940316032963820020113757 9727618512361432507542659)
                  ·
                    refine ⟨14591427768542148761313989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9727618512361432507542659 14591427768542148761313989)
                    ·
                      refine ⟨2735892706601652892746373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14591427768542148761313989 2735892706601652892746373)
                      ·
                        rfl

theorem cell23_5328132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_5328132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328132 prefixEnd_5328132 := by exact prefixLift 5328132
  have htrace : WordTrace (prefixWord ++ tailWord_5328132) baseStart_5328132 baseEnd_5328132 := by
    simpa [prefixWord, tailWord_5328132, baseEnd_5328132] using wordTrace_append hprefix tailTrace_5328132
  have hstable : (prefixWord ++ tailWord_5328132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328132).length < 2 ^ (prefixWord ++ tailWord_5328132).sum := by decide
  have hdescent : baseEnd_5328132 < baseStart_5328132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328145 : List Nat := [1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 4]
def baseStart_5328145 : Nat := 118140960795 + 5328145 * 2 ^ 59
def prefixEnd_5328145 : Nat := 4983230072969 + 3 ^ 40 * 5328145 * 2
def baseEnd_5328145 : Nat := 2735899381850161341883813

theorem tailTrace_5328145 : CollatzResearch.WordTrace tailWord_5328145 prefixEnd_5328145 2735899381850161341883813 := by
  unfold tailWord_5328145
  simp only [CollatzResearch.WordTrace]
  refine ⟨194333413282048114564321889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129555608854698743042881259 194333413282048114564321889)
  ·
    refine ⟨145750059961536085923241417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194333413282048114564321889 145750059961536085923241417)
    ·
      refine ⟨109312544971152064442431063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145750059961536085923241417 109312544971152064442431063)
      ·
        refine ⟨163968817456728096663646595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109312544971152064442431063 163968817456728096663646595)
        ·
          refine ⟨245953226185092144995469893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163968817456728096663646595 245953226185092144995469893)
          ·
            refine ⟨46116229909704777186650605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245953226185092144995469893 46116229909704777186650605)
            ·
              refine ⟨17293586216139291444993977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46116229909704777186650605 17293586216139291444993977)
              ·
                refine ⟨12970189662104468583745483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17293586216139291444993977 12970189662104468583745483)
                ·
                  refine ⟨19455284493156702875618225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12970189662104468583745483 19455284493156702875618225)
                  ·
                    refine ⟨14591463369867527156713669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19455284493156702875618225 14591463369867527156713669)
                    ·
                      refine ⟨2735899381850161341883813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14591463369867527156713669 2735899381850161341883813)
                      ·
                        rfl

theorem cell23_5328145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_5328145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328145 prefixEnd_5328145 := by exact prefixLift 5328145
  have htrace : WordTrace (prefixWord ++ tailWord_5328145) baseStart_5328145 baseEnd_5328145 := by
    simpa [prefixWord, tailWord_5328145, baseEnd_5328145] using wordTrace_append hprefix tailTrace_5328145
  have hstable : (prefixWord ++ tailWord_5328145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328145).length < 2 ^ (prefixWord ++ tailWord_5328145).sum := by decide
  have hdescent : baseEnd_5328145 < baseStart_5328145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328152 : List Nat := [2, 1, 2, 3, 1, 5, 1, 1, 1, 1, 5]
def baseStart_5328152 : Nat := 118140960795 + 5328152 * 2 ^ 59
def prefixEnd_5328152 : Nat := 4983230072969 + 3 ^ 40 * 5328152 * 2
def baseEnd_5328152 : Nat := 2735902976214742814496281

theorem tailTrace_5328152 : CollatzResearch.WordTrace tailWord_5328152 prefixEnd_5328152 2735902976214742814496281 := by
  unfold tailWord_5328152
  simp only [CollatzResearch.WordTrace]
  refine ⟨97166834296511377379913355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129555779062015169839884473 97166834296511377379913355)
  ·
    refine ⟨145750251444767066069870033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97166834296511377379913355 145750251444767066069870033)
    ·
      refine ⟨109312688583575299552402525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145750251444767066069870033 109312688583575299552402525)
      ·
        refine ⟨40992258218840737332150947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109312688583575299552402525 40992258218840737332150947)
        ·
          refine ⟨61488387328261105998226421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40992258218840737332150947 61488387328261105998226421)
          ·
            refine ⟨5764536312024478687333727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61488387328261105998226421 5764536312024478687333727)
            ·
              refine ⟨8646804468036718031000591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5764536312024478687333727 8646804468036718031000591)
              ·
                refine ⟨12970206702055077046500887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8646804468036718031000591 12970206702055077046500887)
                ·
                  refine ⟨19455310053082615569751331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12970206702055077046500887 19455310053082615569751331)
                  ·
                    refine ⟨29182965079623923354626997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19455310053082615569751331 29182965079623923354626997)
                    ·
                      refine ⟨2735902976214742814496281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29182965079623923354626997 2735902976214742814496281)
                      ·
                        rfl

theorem cell23_5328152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_5328152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328152 prefixEnd_5328152 := by exact prefixLift 5328152
  have htrace : WordTrace (prefixWord ++ tailWord_5328152) baseStart_5328152 baseEnd_5328152 := by
    simpa [prefixWord, tailWord_5328152, baseEnd_5328152] using wordTrace_append hprefix tailTrace_5328152
  have hstable : (prefixWord ++ tailWord_5328152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328152).length < 2 ^ (prefixWord ++ tailWord_5328152).sum := by decide
  have hdescent : baseEnd_5328152 < baseStart_5328152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328159 : List Nat := [1, 1, 2, 4, 4, 1, 2, 2, 2, 4]
def baseStart_5328159 : Nat := 118140960795 + 5328159 * 2 ^ 59
def prefixEnd_5328159 : Nat := 4983230072969 + 3 ^ 40 * 5328159 * 2
def baseEnd_5328159 : Nat := 911968856859774762369583

theorem tailTrace_5328159 : CollatzResearch.WordTrace tailWord_5328159 prefixEnd_5328159 911968856859774762369583 := by
  unfold tailWord_5328159
  simp only [CollatzResearch.WordTrace]
  refine ⟨194333923903997394955331531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129555949269331596636887687 194333923903997394955331531)
  ·
    refine ⟨291500885855996092432997297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194333923903997394955331531 291500885855996092432997297)
    ·
      refine ⟨218625664391997069324747973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291500885855996092432997297 218625664391997069324747973)
      ·
        refine ⟨40992312073499450498390245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218625664391997069324747973 40992312073499450498390245)
        ·
          refine ⟨7686058513781146968448171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40992312073499450498390245 7686058513781146968448171)
          ·
            refine ⟨11529087770671720452672257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7686058513781146968448171 11529087770671720452672257)
            ·
              refine ⟨8646815828003790339504193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11529087770671720452672257 8646815828003790339504193)
              ·
                refine ⟨6485111871002842754628145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8646815828003790339504193 6485111871002842754628145)
                ·
                  refine ⟨4863833903252132065971109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6485111871002842754628145 4863833903252132065971109)
                  ·
                    refine ⟨911968856859774762369583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4863833903252132065971109 911968856859774762369583)
                    ·
                      rfl

theorem cell23_5328159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 4].length) (baseStart_5328159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328159 prefixEnd_5328159 := by exact prefixLift 5328159
  have htrace : WordTrace (prefixWord ++ tailWord_5328159) baseStart_5328159 baseEnd_5328159 := by
    simpa [prefixWord, tailWord_5328159, baseEnd_5328159] using wordTrace_append hprefix tailTrace_5328159
  have hstable : (prefixWord ++ tailWord_5328159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328159).length < 2 ^ (prefixWord ++ tailWord_5328159).sum := by decide
  have hdescent : baseEnd_5328159 < baseStart_5328159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328160 : List Nat := [2, 1, 1, 5, 4, 1, 2, 2, 1, 1, 3]
def baseStart_5328160 : Nat := 118140960795 + 5328160 * 2 ^ 59
def prefixEnd_5328160 : Nat := 4983230072969 + 3 ^ 40 * 5328160 * 2
def baseEnd_5328160 : Nat := 2735907084059978783196245

theorem tailTrace_5328160 : CollatzResearch.WordTrace tailWord_5328160 prefixEnd_5328160 2735907084059978783196245 := by
  unfold tailWord_5328160
  simp only [CollatzResearch.WordTrace]
  refine ⟨97166980188496886063058967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129555973584662514750745289 97166980188496886063058967)
  ·
    refine ⟨145750470282745329094588451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97166980188496886063058967 145750470282745329094588451)
    ·
      refine ⟨218625705424117993641882677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145750470282745329094588451 218625705424117993641882677)
      ·
        refine ⟨20496159883511061903926501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 218625705424117993641882677 20496159883511061903926501)
        ·
          refine ⟨3843029978158324106986219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20496159883511061903926501 3843029978158324106986219)
          ·
            refine ⟨5764544967237486160479329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3843029978158324106986219 5764544967237486160479329)
            ·
              refine ⟨4323408725428114620359497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5764544967237486160479329 4323408725428114620359497)
              ·
                refine ⟨3242556544071085965269623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4323408725428114620359497 3242556544071085965269623)
                ·
                  refine ⟨4863834816106628947904435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3242556544071085965269623 4863834816106628947904435)
                  ·
                    refine ⟨7295752224159943421856653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4863834816106628947904435 7295752224159943421856653)
                    ·
                      refine ⟨2735907084059978783196245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7295752224159943421856653 2735907084059978783196245)
                      ·
                        rfl

theorem cell23_5328160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_5328160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328160 prefixEnd_5328160 := by exact prefixLift 5328160
  have htrace : WordTrace (prefixWord ++ tailWord_5328160) baseStart_5328160 baseEnd_5328160 := by
    simpa [prefixWord, tailWord_5328160, baseEnd_5328160] using wordTrace_append hprefix tailTrace_5328160
  have hstable : (prefixWord ++ tailWord_5328160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328160).length < 2 ^ (prefixWord ++ tailWord_5328160).sum := by decide
  have hdescent : baseEnd_5328160 < baseStart_5328160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328189 : List Nat := [1, 4, 1, 5, 1, 1, 3, 7]
def baseStart_5328189 : Nat := 118140960795 + 5328189 * 2 ^ 59
def prefixEnd_5328189 : Nat := 4983230072969 + 3 ^ 40 * 5328189 * 2
def baseEnd_5328189 : Nat := 101330443518479969249393

theorem tailTrace_5328189 : CollatzResearch.WordTrace tailWord_5328189 prefixEnd_5328189 101330443518479969249393 := by
  unfold tailWord_5328189
  simp only [CollatzResearch.WordTrace]
  refine ⟨194335018093888710078923621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129556678729259140052615747 194335018093888710078923621)
  ·
    refine ⟨36437815892604133139798179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194335018093888710078923621 36437815892604133139798179)
    ·
      refine ⟨54656723838906199709697269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36437815892604133139798179 54656723838906199709697269)
      ·
        refine ⟨5124067859897456222784119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54656723838906199709697269 5124067859897456222784119)
        ·
          refine ⟨7686101789846184334176179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5124067859897456222784119 7686101789846184334176179)
          ·
            refine ⟨11529152684769276501264269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7686101789846184334176179 11529152684769276501264269)
            ·
              refine ⟨4323432256788478687974101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11529152684769276501264269 4323432256788478687974101)
              ·
                refine ⟨101330443518479969249393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4323432256788478687974101 101330443518479969249393)
                ·
                  rfl

theorem cell23_5328189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 7].length) (baseStart_5328189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328189 prefixEnd_5328189 := by exact prefixLift 5328189
  have htrace : WordTrace (prefixWord ++ tailWord_5328189) baseStart_5328189 baseEnd_5328189 := by
    simpa [prefixWord, tailWord_5328189, baseEnd_5328189] using wordTrace_append hprefix tailTrace_5328189
  have hstable : (prefixWord ++ tailWord_5328189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328189).length < 2 ^ (prefixWord ++ tailWord_5328189).sum := by decide
  have hdescent : baseEnd_5328189 < baseStart_5328189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328192 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 3, 3, 2]
def baseStart_5328192 : Nat := 118140960795 + 5328192 * 2 ^ 59
def prefixEnd_5328192 : Nat := 4983230072969 + 3 ^ 40 * 5328192 * 2
def baseEnd_5328192 : Nat := 2735923515440922657996097

theorem tailTrace_5328192 : CollatzResearch.WordTrace tailWord_5328192 prefixEnd_5328192 2735923515440922657996097 := by
  unfold tailWord_5328192
  simp only [CollatzResearch.WordTrace]
  refine ⟨97167563756438920795641415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129556751675251894394188553 97167563756438920795641415)
  ·
    refine ⟨145751345634658381193462123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97167563756438920795641415 145751345634658381193462123)
    ·
      refine ⟨218627018451987571790193185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145751345634658381193462123 218627018451987571790193185)
      ·
        refine ⟨163970263838990678842644889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218627018451987571790193185 163970263838990678842644889)
        ·
          refine ⟨122977697879243009131983667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163970263838990678842644889 122977697879243009131983667)
          ·
            refine ⟨184466546818864513697975501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122977697879243009131983667 184466546818864513697975501)
            ·
              refine ⟨69174955057074192636740813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184466546818864513697975501 69174955057074192636740813)
              ·
                refine ⟨25940608146402822238777805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69174955057074192636740813 25940608146402822238777805)
                ·
                  refine ⟨9727728054901058339541677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25940608146402822238777805 9727728054901058339541677)
                  ·
                    refine ⟨3647898020587896877328129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9727728054901058339541677 3647898020587896877328129)
                    ·
                      refine ⟨2735923515440922657996097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3647898020587896877328129 2735923515440922657996097)
                      ·
                        rfl

theorem cell23_5328192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 3, 3, 2].length) (baseStart_5328192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328192 prefixEnd_5328192 := by exact prefixLift 5328192
  have htrace : WordTrace (prefixWord ++ tailWord_5328192) baseStart_5328192 baseEnd_5328192 := by
    simpa [prefixWord, tailWord_5328192, baseEnd_5328192] using wordTrace_append hprefix tailTrace_5328192
  have hstable : (prefixWord ++ tailWord_5328192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328192).length < 2 ^ (prefixWord ++ tailWord_5328192).sum := by decide
  have hdescent : baseEnd_5328192 < baseStart_5328192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328209 : List Nat := [1, 2, 2, 1, 4, 1, 3, 3, 1, 3, 2]
def baseStart_5328209 : Nat := 118140960795 + 5328209 * 2 ^ 59
def prefixEnd_5328209 : Nat := 4983230072969 + 3 ^ 40 * 5328209 * 2
def baseEnd_5328209 : Nat := 2735932244612049091483519

theorem tailTrace_5328209 : CollatzResearch.WordTrace tailWord_5328209 prefixEnd_5328209 2735932244612049091483519 := by
  unfold tailWord_5328209
  simp only [CollatzResearch.WordTrace]
  refine ⟨194335747553816253494651681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129557165035877502329767787 194335747553816253494651681)
  ·
    refine ⟨145751810665362190120988761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194335747553816253494651681 145751810665362190120988761)
    ·
      refine ⟨109313857999021642590741571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145751810665362190120988761 109313857999021642590741571)
      ·
        refine ⟨163970786998532463886112357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109313857999021642590741571 163970786998532463886112357)
        ·
          refine ⟨30744522562224836978646067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163970786998532463886112357 30744522562224836978646067)
          ·
            refine ⟨46116783843337255467969101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30744522562224836978646067 46116783843337255467969101)
            ·
              refine ⟨17293793941251470800488413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46116783843337255467969101 17293793941251470800488413)
              ·
                refine ⟨6485172727969301550183155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17293793941251470800488413 6485172727969301550183155)
                ·
                  refine ⟨9727759091953952325274733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6485172727969301550183155 9727759091953952325274733)
                  ·
                    refine ⟨3647909659482732121978025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9727759091953952325274733 3647909659482732121978025)
                    ·
                      refine ⟨2735932244612049091483519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3647909659482732121978025 2735932244612049091483519)
                      ·
                        rfl

theorem cell23_5328209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 3, 2].length) (baseStart_5328209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328209 prefixEnd_5328209 := by exact prefixLift 5328209
  have htrace : WordTrace (prefixWord ++ tailWord_5328209) baseStart_5328209 baseEnd_5328209 := by
    simpa [prefixWord, tailWord_5328209, baseEnd_5328209] using wordTrace_append hprefix tailTrace_5328209
  have hstable : (prefixWord ++ tailWord_5328209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328209).length < 2 ^ (prefixWord ++ tailWord_5328209).sum := by decide
  have hdescent : baseEnd_5328209 < baseStart_5328209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328215 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 2, 6]
def baseStart_5328215 : Nat := 118140960795 + 5328215 * 2 ^ 59
def prefixEnd_5328215 : Nat := 4983230072969 + 3 ^ 40 * 5328215 * 2
def baseEnd_5328215 : Nat := 911978441831992022669497

theorem tailTrace_5328215 : CollatzResearch.WordTrace tailWord_5328215 prefixEnd_5328215 911978441831992022669497 := by
  unfold tailWord_5328215
  simp only [CollatzResearch.WordTrace]
  refine ⟨194335966391794516519370099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129557310927863011012913399 194335966391794516519370099)
  ·
    refine ⟨291503949587691774779055149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194335966391794516519370099 291503949587691774779055149)
    ·
      refine ⟨109313981095384415542145681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291503949587691774779055149 109313981095384415542145681)
      ·
        refine ⟨81985485821538311656609261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109313981095384415542145681 81985485821538311656609261)
        ·
          refine ⟨30744557183076866871228473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81985485821538311656609261 30744557183076866871228473)
          ·
            refine ⟨23058417887307650153421355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30744557183076866871228473 23058417887307650153421355)
            ·
              refine ⟨34587626830961475230132033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23058417887307650153421355 34587626830961475230132033)
              ·
                refine ⟨25940720123221106422599025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34587626830961475230132033 25940720123221106422599025)
                ·
                  refine ⟨19455540092415829816949269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25940720123221106422599025 19455540092415829816949269)
                  ·
                    refine ⟨911978441831992022669497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19455540092415829816949269 911978441831992022669497)
                    ·
                      rfl

theorem cell23_5328215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_5328215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328215 prefixEnd_5328215 := by exact prefixLift 5328215
  have htrace : WordTrace (prefixWord ++ tailWord_5328215) baseStart_5328215 baseEnd_5328215 := by
    simpa [prefixWord, tailWord_5328215, baseEnd_5328215] using wordTrace_append hprefix tailTrace_5328215
  have hstable : (prefixWord ++ tailWord_5328215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328215).length < 2 ^ (prefixWord ++ tailWord_5328215).sum := by decide
  have hdescent : baseEnd_5328215 < baseStart_5328215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328225 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 1, 6, 3]
def baseStart_5328225 : Nat := 118140960795 + 5328225 * 2 ^ 59
def prefixEnd_5328225 : Nat := 4983230072969 + 3 ^ 40 * 5328225 * 2
def baseEnd_5328225 : Nat := 2735940460302521028883445

theorem tailTrace_5328225 : CollatzResearch.WordTrace tailWord_5328225 prefixEnd_5328225 2735940460302521028883445 := by
  unfold tailWord_5328225
  simp only [CollatzResearch.WordTrace]
  refine ⟨194336331121758288227234129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129557554081172192151489419 194336331121758288227234129)
  ·
    refine ⟨145752248341318716170425597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194336331121758288227234129 145752248341318716170425597)
    ·
      refine ⟨54657093127994518563909599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145752248341318716170425597 54657093127994518563909599)
      ·
        refine ⟨81985639691991777845864399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54657093127994518563909599 81985639691991777845864399)
        ·
          refine ⟨122978459537987666768796599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81985639691991777845864399 122978459537987666768796599)
          ·
            refine ⟨184467689306981500153194899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122978459537987666768796599 184467689306981500153194899)
            ·
              refine ⟨276701533960472250229792349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184467689306981500153194899 276701533960472250229792349)
              ·
                refine ⟨103763075235177093836172131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276701533960472250229792349 103763075235177093836172131)
                ·
                  refine ⟨155644612852765640754258197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103763075235177093836172131 155644612852765640754258197)
                  ·
                    refine ⟨7295841227473389410355853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 155644612852765640754258197 7295841227473389410355853)
                    ·
                      refine ⟨2735940460302521028883445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7295841227473389410355853 2735940460302521028883445)
                      ·
                        rfl

theorem cell23_5328225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_5328225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328225 prefixEnd_5328225 := by exact prefixLift 5328225
  have htrace : WordTrace (prefixWord ++ tailWord_5328225) baseStart_5328225 baseEnd_5328225 := by
    simpa [prefixWord, tailWord_5328225, baseEnd_5328225] using wordTrace_append hprefix tailTrace_5328225
  have hstable : (prefixWord ++ tailWord_5328225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328225).length < 2 ^ (prefixWord ++ tailWord_5328225).sum := by decide
  have hdescent : baseEnd_5328225 < baseStart_5328225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328290 : List Nat := [3, 3, 1, 2, 1, 4, 2, 1, 2, 2, 2]
def baseStart_5328290 : Nat := 118140960795 + 5328290 * 2 ^ 59
def prefixEnd_5328290 : Nat := 4983230072969 + 3 ^ 40 * 5328290 * 2
def baseEnd_5328290 : Nat := 2735973836545063274570647

theorem tailTrace_5328290 : CollatzResearch.WordTrace tailWord_5328290 prefixEnd_5328290 2735973836545063274570647 := by
  unfold tailWord_5328290
  simp only [CollatzResearch.WordTrace]
  refine ⟨48584675466630701082087581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129559134577681869552233549 48584675466630701082087581)
  ·
    refine ⟨18219253299986512905782843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48584675466630701082087581 18219253299986512905782843)
    ·
      refine ⟨27328879949979769358674265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18219253299986512905782843 27328879949979769358674265)
      ·
        refine ⟨20496659962484827019005699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27328879949979769358674265 20496659962484827019005699)
        ·
          refine ⟨30744989943727240528508549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20496659962484827019005699 30744989943727240528508549)
          ·
            refine ⟨5764685614448857599095353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30744989943727240528508549 5764685614448857599095353)
            ·
              refine ⟨4323514210836643199321515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5764685614448857599095353 4323514210836643199321515)
              ·
                refine ⟨6485271316254964798982273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4323514210836643199321515 6485271316254964798982273)
                ·
                  refine ⟨4863953487191223599236705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6485271316254964798982273 4863953487191223599236705)
                  ·
                    refine ⟨3647965115393417699427529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4863953487191223599236705 3647965115393417699427529)
                    ·
                      refine ⟨2735973836545063274570647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3647965115393417699427529 2735973836545063274570647)
                      ·
                        rfl

theorem cell23_5328290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_5328290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328290 prefixEnd_5328290 := by exact prefixLift 5328290
  have htrace : WordTrace (prefixWord ++ tailWord_5328290) baseStart_5328290 baseEnd_5328290 := by
    simpa [prefixWord, tailWord_5328290, baseEnd_5328290] using wordTrace_append hprefix tailTrace_5328290
  have hstable : (prefixWord ++ tailWord_5328290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328290).length < 2 ^ (prefixWord ++ tailWord_5328290).sum := by decide
  have hdescent : baseEnd_5328290 < baseStart_5328290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328309 : List Nat := [1, 3, 3, 2, 2, 2, 2, 1, 2, 5]
def baseStart_5328309 : Nat := 118140960795 + 5328309 * 2 ^ 59
def prefixEnd_5328309 : Nat := 4983230072969 + 3 ^ 40 * 5328309 * 2
def baseEnd_5328309 : Nat := 911994530892499566744353

theorem tailTrace_5328309 : CollatzResearch.WordTrace tailWord_5328309 prefixEnd_5328309 911994530892499566744353 := by
  unfold tailWord_5328309
  simp only [CollatzResearch.WordTrace]
  refine ⟨194339394853453970573291981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129559596568969313715527987 194339394853453970573291981)
  ·
    refine ⟨72877273070045238964984493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194339394853453970573291981 72877273070045238964984493)
    ·
      refine ⟨27328977401266964611869185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72877273070045238964984493 27328977401266964611869185)
      ·
        refine ⟨20496733050950223458901889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27328977401266964611869185 20496733050950223458901889)
        ·
          refine ⟨15372549788212667594176417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20496733050950223458901889 15372549788212667594176417)
          ·
            refine ⟨11529412341159500695632313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15372549788212667594176417 11529412341159500695632313)
            ·
              refine ⟨8647059255869625521724235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11529412341159500695632313 8647059255869625521724235)
              ·
                refine ⟨12970588883804438282586353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8647059255869625521724235 12970588883804438282586353)
                ·
                  refine ⟨9727941662853328711939765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12970588883804438282586353 9727941662853328711939765)
                  ·
                    refine ⟨911994530892499566744353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9727941662853328711939765 911994530892499566744353)
                    ·
                      rfl

theorem cell23_5328309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_5328309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328309 prefixEnd_5328309 := by exact prefixLift 5328309
  have htrace : WordTrace (prefixWord ++ tailWord_5328309) baseStart_5328309 baseEnd_5328309 := by
    simpa [prefixWord, tailWord_5328309, baseEnd_5328309] using wordTrace_append hprefix tailTrace_5328309
  have hstable : (prefixWord ++ tailWord_5328309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328309).length < 2 ^ (prefixWord ++ tailWord_5328309).sum := by decide
  have hdescent : baseEnd_5328309 < baseStart_5328309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328312 : List Nat := [2, 1, 2, 1, 2, 2, 3, 3, 2, 1, 4]
def baseStart_5328312 : Nat := 118140960795 + 5328312 * 2 ^ 59
def prefixEnd_5328312 : Nat := 4983230072969 + 3 ^ 40 * 5328312 * 2
def baseEnd_5328312 : Nat := 2735985133119462188495545

theorem tailTrace_5328312 : CollatzResearch.WordTrace tailWord_5328312 prefixEnd_5328312 2735985133119462188495545 := by
  unfold tailWord_5328312
  simp only [CollatzResearch.WordTrace]
  refine ⟨97169752136221551042825595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129559669514962068057100793 97169752136221551042825595)
  ·
    refine ⟨145754628204332326564238393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97169752136221551042825595 145754628204332326564238393)
    ·
      refine ⟨109315971153249244923178795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145754628204332326564238393 109315971153249244923178795)
      ·
        refine ⟨163973956729873867384768193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109315971153249244923178795 163973956729873867384768193)
        ·
          refine ⟨122980467547405400538576145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163973956729873867384768193 122980467547405400538576145)
          ·
            refine ⟨92235350660554050403932109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122980467547405400538576145 92235350660554050403932109)
            ·
              refine ⟨34588256497707768901474541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92235350660554050403932109 34588256497707768901474541)
              ·
                refine ⟨12970596186640413338052953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34588256497707768901474541 12970596186640413338052953)
                ·
                  refine ⟨9727947139980310003539715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12970596186640413338052953 9727947139980310003539715)
                  ·
                    refine ⟨14591920709970465005309573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9727947139980310003539715 14591920709970465005309573)
                    ·
                      refine ⟨2735985133119462188495545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14591920709970465005309573 2735985133119462188495545)
                      ·
                        rfl

theorem cell23_5328312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_5328312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328312 prefixEnd_5328312 := by exact prefixLift 5328312
  have htrace : WordTrace (prefixWord ++ tailWord_5328312) baseStart_5328312 baseEnd_5328312 := by
    simpa [prefixWord, tailWord_5328312, baseEnd_5328312] using wordTrace_append hprefix tailTrace_5328312
  have hstable : (prefixWord ++ tailWord_5328312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328312).length < 2 ^ (prefixWord ++ tailWord_5328312).sum := by decide
  have hdescent : baseEnd_5328312 < baseStart_5328312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328335 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 8]
def baseStart_5328335 : Nat := 118140960795 + 5328335 * 2 ^ 59
def prefixEnd_5328335 : Nat := 4983230072969 + 3 ^ 40 * 5328335 * 2
def baseEnd_5328335 : Nat := 303999660352723955389771

theorem tailTrace_5328335 : CollatzResearch.WordTrace tailWord_5328335 prefixEnd_5328335 303999660352723955389771 := by
  unfold tailWord_5328335
  simp only [CollatzResearch.WordTrace]
  refine ⟨194340343151359777013738459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129560228767573184675825639 194340343151359777013738459)
  ·
    refine ⟨291510514727039665520607689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194340343151359777013738459 291510514727039665520607689)
    ·
      refine ⟨218632886045279749140455767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291510514727039665520607689 218632886045279749140455767)
      ·
        refine ⟨327949329067919623710683651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218632886045279749140455767 327949329067919623710683651)
        ·
          refine ⟨491923993601879435566025477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327949329067919623710683651 491923993601879435566025477)
          ·
            refine ⟨92235748800352394168629777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 491923993601879435566025477 92235748800352394168629777)
            ·
              refine ⟨69176811600264295626472333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92235748800352394168629777 69176811600264295626472333)
              ·
                refine ⟨25941304350099110859927125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69176811600264295626472333 25941304350099110859927125)
                ·
                  refine ⟨303999660352723955389771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25941304350099110859927125 303999660352723955389771)
                  ·
                    rfl

theorem cell23_5328335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 8].length) (baseStart_5328335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328335 prefixEnd_5328335 := by exact prefixLift 5328335
  have htrace : WordTrace (prefixWord ++ tailWord_5328335) baseStart_5328335 baseEnd_5328335 := by
    simpa [prefixWord, tailWord_5328335, baseEnd_5328335] using wordTrace_append hprefix tailTrace_5328335
  have hstable : (prefixWord ++ tailWord_5328335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328335).length < 2 ^ (prefixWord ++ tailWord_5328335).sum := by decide
  have hdescent : baseEnd_5328335 < baseStart_5328335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328373 : List Nat := [1, 3, 5, 1, 1, 1, 1, 5, 1, 4]
def baseStart_5328373 : Nat := 118140960795 + 5328373 * 2 ^ 59
def prefixEnd_5328373 : Nat := 4983230072969 + 3 ^ 40 * 5328373 * 2
def baseEnd_5328373 : Nat := 912005485146462149944255

theorem tailTrace_5328373 : CollatzResearch.WordTrace tailWord_5328373 prefixEnd_5328373 912005485146462149944255 := by
  unfold tailWord_5328373
  simp only [CollatzResearch.WordTrace]
  refine ⟨194341729125222109503621773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129561152750148073002414515 194341729125222109503621773)
  ·
    refine ⟨72878148421958291063858165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194341729125222109503621773 72878148421958291063858165)
    ·
      refine ⟨6832326414558589787236703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72878148421958291063858165 6832326414558589787236703)
      ·
        refine ⟨10248489621837884680855055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6832326414558589787236703 10248489621837884680855055)
        ·
          refine ⟨15372734432756827021282583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10248489621837884680855055 15372734432756827021282583)
          ·
            refine ⟨23059101649135240531923875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15372734432756827021282583 23059101649135240531923875)
            ·
              refine ⟨34588652473702860797885813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23059101649135240531923875 34588652473702860797885813)
              ·
                refine ⟨3242686169409643199801795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34588652473702860797885813 3242686169409643199801795)
                ·
                  refine ⟨4864029254114464799702693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3242686169409643199801795 4864029254114464799702693)
                  ·
                    refine ⟨912005485146462149944255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4864029254114464799702693 912005485146462149944255)
                    ·
                      rfl

theorem cell23_5328373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_5328373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328373 prefixEnd_5328373 := by exact prefixLift 5328373
  have htrace : WordTrace (prefixWord ++ tailWord_5328373) baseStart_5328373 baseEnd_5328373 := by
    simpa [prefixWord, tailWord_5328373, baseEnd_5328373] using wordTrace_append hprefix tailTrace_5328373
  have hstable : (prefixWord ++ tailWord_5328373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328373).length < 2 ^ (prefixWord ++ tailWord_5328373).sum := by decide
  have hdescent : baseEnd_5328373 < baseStart_5328373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328386 : List Nat := [3, 4, 1, 2, 1, 1, 3, 2, 6]
def baseStart_5328386 : Nat := 118140960795 + 5328386 * 2 ^ 59
def prefixEnd_5328386 : Nat := 4983230072969 + 3 ^ 40 * 5328386 * 2
def baseEnd_5328386 : Nat := 304002570076432766552245

theorem tailTrace_5328386 : CollatzResearch.WordTrace tailWord_5328386 prefixEnd_5328386 304002570076432766552245 := by
  unfold tailWord_5328386
  simp only [CollatzResearch.WordTrace]
  refine ⟨48585550818543753180961253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129561468849450008482563341 48585550818543753180961253)
  ·
    refine ⟨9109790778476953721430235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48585550818543753180961253 9109790778476953721430235)
    ·
      refine ⟨13664686167715430582145353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9109790778476953721430235 13664686167715430582145353)
      ·
        refine ⟨10248514625786572936609015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13664686167715430582145353 10248514625786572936609015)
        ·
          refine ⟨15372771938679859404913523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10248514625786572936609015 15372771938679859404913523)
          ·
            refine ⟨23059157908019789107370285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15372771938679859404913523 23059157908019789107370285)
            ·
              refine ⟨8647184215507420915263857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23059157908019789107370285 8647184215507420915263857)
              ·
                refine ⟨6485388161630565686447893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8647184215507420915263857 6485388161630565686447893)
                ·
                  refine ⟨304002570076432766552245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6485388161630565686447893 304002570076432766552245)
                  ·
                    rfl

theorem cell23_5328386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_5328386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328386 prefixEnd_5328386 := by exact prefixLift 5328386
  have htrace : WordTrace (prefixWord ++ tailWord_5328386) baseStart_5328386 baseEnd_5328386 := by
    simpa [prefixWord, tailWord_5328386, baseEnd_5328386] using wordTrace_append hprefix tailTrace_5328386
  have hstable : (prefixWord ++ tailWord_5328386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328386).length < 2 ^ (prefixWord ++ tailWord_5328386).sum := by decide
  have hdescent : baseEnd_5328386 < baseStart_5328386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328389 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 4, 3, 2]
def baseStart_5328389 : Nat := 118140960795 + 5328389 * 2 ^ 59
def prefixEnd_5328389 : Nat := 4983230072969 + 3 ^ 40 * 5328389 * 2
def baseEnd_5328389 : Nat := 2736024671129858387232691

theorem tailTrace_5328389 : CollatzResearch.WordTrace tailWord_5328389 prefixEnd_5328389 2736024671129858387232691 := by
  unfold tailWord_5328389
  simp only [CollatzResearch.WordTrace]
  refine ⟨194342312693164144236204221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129561541795442762824136147 194342312693164144236204221)
  ·
    refine ⟨72878367259936554088576583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194342312693164144236204221 72878367259936554088576583)
    ·
      refine ⟨109317550889904831132864875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72878367259936554088576583 109317550889904831132864875)
      ·
        refine ⟨163976326334857246699297313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109317550889904831132864875 163976326334857246699297313)
        ·
          refine ⟨122982244751142935024472985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163976326334857246699297313 122982244751142935024472985)
          ·
            refine ⟨92236683563357201268354739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122982244751142935024472985 92236683563357201268354739)
            ·
              refine ⟨138355025345035801902532109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92236683563357201268354739 138355025345035801902532109)
              ·
                refine ⟨51883134504388425713449541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138355025345035801902532109 51883134504388425713449541)
                ·
                  refine ⟨9728087719572829821271789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51883134504388425713449541 9728087719572829821271789)
                  ·
                    refine ⟨3648032894839811182976921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9728087719572829821271789 3648032894839811182976921)
                    ·
                      refine ⟨2736024671129858387232691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3648032894839811182976921 2736024671129858387232691)
                      ·
                        rfl

theorem cell23_5328389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 3, 2].length) (baseStart_5328389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328389 prefixEnd_5328389 := by exact prefixLift 5328389
  have htrace : WordTrace (prefixWord ++ tailWord_5328389) baseStart_5328389 baseEnd_5328389 := by
    simpa [prefixWord, tailWord_5328389, baseEnd_5328389] using wordTrace_append hprefix tailTrace_5328389
  have hstable : (prefixWord ++ tailWord_5328389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328389).length < 2 ^ (prefixWord ++ tailWord_5328389).sum := by decide
  have hdescent : baseEnd_5328389 < baseStart_5328389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328416 : List Nat := [2, 1, 1, 6, 1, 2, 2, 2, 1, 5]
def baseStart_5328416 : Nat := 118140960795 + 5328416 * 2 ^ 59
def prefixEnd_5328416 : Nat := 4983230072969 + 3 ^ 40 * 5328416 * 2
def baseEnd_5328416 : Nat := 912012845035843260531689

theorem tailTrace_5328416 : CollatzResearch.WordTrace tailWord_5328416 prefixEnd_5328416 912012845035843260531689 := by
  unfold tailWord_5328416
  simp only [CollatzResearch.WordTrace]
  refine ⟨97171648732033163923718551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129562198309377551898291401 97171648732033163923718551)
  ·
    refine ⟨145757473098049745885577827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97171648732033163923718551 145757473098049745885577827)
    ·
      refine ⟨218636209647074618828366741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145757473098049745885577827 218636209647074618828366741)
      ·
        refine ⟨10248572327206622757579691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 218636209647074618828366741 10248572327206622757579691)
        ·
          refine ⟨15372858490809934136369537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10248572327206622757579691 15372858490809934136369537)
          ·
            refine ⟨11529643868107450602277153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15372858490809934136369537 11529643868107450602277153)
            ·
              refine ⟨8647232901080587951707865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11529643868107450602277153 8647232901080587951707865)
              ·
                refine ⟨6485424675810440963780899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8647232901080587951707865 6485424675810440963780899)
                ·
                  refine ⟨9728137013715661445671349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6485424675810440963780899 9728137013715661445671349)
                  ·
                    refine ⟨912012845035843260531689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9728137013715661445671349 912012845035843260531689)
                    ·
                      rfl

theorem cell23_5328416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 1, 5].length) (baseStart_5328416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328416 prefixEnd_5328416 := by exact prefixLift 5328416
  have htrace : WordTrace (prefixWord ++ tailWord_5328416) baseStart_5328416 baseEnd_5328416 := by
    simpa [prefixWord, tailWord_5328416, baseEnd_5328416] using wordTrace_append hprefix tailTrace_5328416
  have hstable : (prefixWord ++ tailWord_5328416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328416).length < 2 ^ (prefixWord ++ tailWord_5328416).sum := by decide
  have hdescent : baseEnd_5328416 < baseStart_5328416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328430 : List Nat := [4, 1, 3, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_5328430 : Nat := 118140960795 + 5328430 * 2 ^ 59
def prefixEnd_5328430 : Nat := 4983230072969 + 3 ^ 40 * 5328430 * 2
def baseEnd_5328430 : Nat := 2736045723836692726820003

theorem tailTrace_5328430 : CollatzResearch.WordTrace tailWord_5328430 prefixEnd_5328430 2736045723836692726820003 := by
  unfold tailWord_5328430
  simp only [CollatzResearch.WordTrace]
  refine ⟨24292976010751951029805843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129562538724010405492297829 24292976010751951029805843)
  ·
    refine ⟨36439464016127926544708765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24292976010751951029805843 36439464016127926544708765)
    ·
      refine ⟨13664799006047972454265787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36439464016127926544708765 13664799006047972454265787)
      ·
        refine ⟨20497198509071958681398681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13664799006047972454265787 20497198509071958681398681)
        ·
          refine ⟨15372898881803969011049011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20497198509071958681398681 15372898881803969011049011)
          ·
            refine ⟨23059348322705953516573517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15372898881803969011049011 23059348322705953516573517)
            ·
              refine ⟨8647255621014732568715069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23059348322705953516573517 8647255621014732568715069)
              ·
                refine ⟨3242720857880524713268151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8647255621014732568715069 3242720857880524713268151)
                ·
                  refine ⟨4864081286820787069902227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3242720857880524713268151 4864081286820787069902227)
                  ·
                    refine ⟨7296121930231180604853341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4864081286820787069902227 7296121930231180604853341)
                    ·
                      refine ⟨2736045723836692726820003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7296121930231180604853341 2736045723836692726820003)
                      ·
                        rfl

theorem cell23_5328430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_5328430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328430 prefixEnd_5328430 := by exact prefixLift 5328430
  have htrace : WordTrace (prefixWord ++ tailWord_5328430) baseStart_5328430 baseEnd_5328430 := by
    simpa [prefixWord, tailWord_5328430, baseEnd_5328430] using wordTrace_append hprefix tailTrace_5328430
  have hstable : (prefixWord ++ tailWord_5328430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328430).length < 2 ^ (prefixWord ++ tailWord_5328430).sum := by decide
  have hdescent : baseEnd_5328430 < baseStart_5328430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328432 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 4]
def baseStart_5328432 : Nat := 118140960795 + 5328432 * 2 ^ 59
def prefixEnd_5328432 : Nat := 4983230072969 + 3 ^ 40 * 5328432 * 2
def baseEnd_5328432 : Nat := 2736046750798001718994993

theorem tailTrace_5328432 : CollatzResearch.WordTrace tailWord_5328432 prefixEnd_5328432 2736046750798001718994993 := by
  unfold tailWord_5328432
  simp only [CollatzResearch.WordTrace]
  refine ⟨97171940516004181290009775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129562587354672241720013033 97171940516004181290009775)
  ·
    refine ⟨145757910774006271935014663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97171940516004181290009775 145757910774006271935014663)
    ·
      refine ⟨218636866161009407902521995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145757910774006271935014663 218636866161009407902521995)
      ·
        refine ⟨327955299241514111853782993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218636866161009407902521995 327955299241514111853782993)
        ·
          refine ⟨245966474431135583890337245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327955299241514111853782993 245966474431135583890337245)
          ·
            refine ⟨92237427911675843958876467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245966474431135583890337245 92237427911675843958876467)
            ·
              refine ⟨138356141867513765938314701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92237427911675843958876467 138356141867513765938314701)
              ·
                refine ⟨51883553200317662226868013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138356141867513765938314701 51883553200317662226868013)
                ·
                  refine ⟨19456332450119123335075505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51883553200317662226868013 19456332450119123335075505)
                  ·
                    refine ⟨14592249337589342501306629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19456332450119123335075505 14592249337589342501306629)
                    ·
                      refine ⟨2736046750798001718994993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14592249337589342501306629 2736046750798001718994993)
                      ·
                        rfl

theorem cell23_5328432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_5328432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328432 prefixEnd_5328432 := by exact prefixLift 5328432
  have htrace : WordTrace (prefixWord ++ tailWord_5328432) baseStart_5328432 baseEnd_5328432 := by
    simpa [prefixWord, tailWord_5328432, baseEnd_5328432] using wordTrace_append hprefix tailTrace_5328432
  have hstable : (prefixWord ++ tailWord_5328432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328432).length < 2 ^ (prefixWord ++ tailWord_5328432).sum := by decide
  have hdescent : baseEnd_5328432 < baseStart_5328432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328439 : List Nat := [1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 5]
def baseStart_5328439 : Nat := 118140960795 + 5328439 * 2 ^ 59
def prefixEnd_5328439 : Nat := 4983230072969 + 3 ^ 40 * 5328439 * 2
def baseEnd_5328439 : Nat := 2736050345162583191607461

theorem tailTrace_5328439 : CollatzResearch.WordTrace tailWord_5328439 prefixEnd_5328439 2736050345162583191607461 := by
  unfold tailWord_5328439
  simp only [CollatzResearch.WordTrace]
  refine ⟨194344136342983002775524371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129562757561988668517016247 194344136342983002775524371)
  ·
    refine ⟨291516204514474504163286557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194344136342983002775524371 291516204514474504163286557)
    ·
      refine ⟨109318576692927939061232459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291516204514474504163286557 109318576692927939061232459)
      ·
        refine ⟨163977865039391908591848689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109318576692927939061232459 163977865039391908591848689)
        ·
          refine ⟨122983398779543931443886517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163977865039391908591848689 122983398779543931443886517)
          ·
            refine ⟨11529693635582243572864361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122983398779543931443886517 11529693635582243572864361)
            ·
              refine ⟨8647270226686682679648271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11529693635582243572864361 8647270226686682679648271)
              ·
                refine ⟨12970905340030024019472407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8647270226686682679648271 12970905340030024019472407)
                ·
                  refine ⟨19456358010045036029208611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12970905340030024019472407 19456358010045036029208611)
                  ·
                    refine ⟨29184537015067554043812917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19456358010045036029208611 29184537015067554043812917)
                    ·
                      refine ⟨2736050345162583191607461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29184537015067554043812917 2736050345162583191607461)
                      ·
                        rfl

theorem cell23_5328439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_5328439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328439 prefixEnd_5328439 := by exact prefixLift 5328439
  have htrace : WordTrace (prefixWord ++ tailWord_5328439) baseStart_5328439 baseEnd_5328439 := by
    simpa [prefixWord, tailWord_5328439, baseEnd_5328439] using wordTrace_append hprefix tailTrace_5328439
  have hstable : (prefixWord ++ tailWord_5328439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328439).length < 2 ^ (prefixWord ++ tailWord_5328439).sum := by decide
  have hdescent : baseEnd_5328439 < baseStart_5328439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328462 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_5328462 : Nat := 118140960795 + 5328462 * 2 ^ 59
def prefixEnd_5328462 : Nat := 4983230072969 + 3 ^ 40 * 5328462 * 2
def baseEnd_5328462 : Nat := 2736062155217636601619855

theorem tailTrace_5328462 : CollatzResearch.WordTrace tailWord_5328462 prefixEnd_5328462 2736062155217636601619855 := by
  unfold tailWord_5328462
  simp only [CollatzResearch.WordTrace]
  refine ⟨24293121902737459712951455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129563316814599785135741093 24293121902737459712951455)
  ·
    refine ⟨36439682854106189569427183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24293121902737459712951455 36439682854106189569427183)
    ·
      refine ⟨54659524281159284354140775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36439682854106189569427183 54659524281159284354140775)
      ·
        refine ⟨81989286421738926531211163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54659524281159284354140775 81989286421738926531211163)
        ·
          refine ⟨122983929632608389796816745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81989286421738926531211163 122983929632608389796816745)
          ·
            refine ⟨92237947224456292347612559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122983929632608389796816745 92237947224456292347612559)
            ·
              refine ⟨138356920836684438521418839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92237947224456292347612559 138356920836684438521418839)
              ·
                refine ⟨207535381255026657782128259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138356920836684438521418839 207535381255026657782128259)
                ·
                  refine ⟨311303071882539986673192389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207535381255026657782128259 311303071882539986673192389)
                  ·
                    refine ⟨58369325977976247501223573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 311303071882539986673192389 58369325977976247501223573)
                    ·
                      refine ⟨2736062155217636601619855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58369325977976247501223573 2736062155217636601619855)
                      ·
                        rfl

theorem cell23_5328462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_5328462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328462 prefixEnd_5328462 := by exact prefixLift 5328462
  have htrace : WordTrace (prefixWord ++ tailWord_5328462) baseStart_5328462 baseEnd_5328462 := by
    simpa [prefixWord, tailWord_5328462, baseEnd_5328462] using wordTrace_append hprefix tailTrace_5328462
  have hstable : (prefixWord ++ tailWord_5328462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328462).length < 2 ^ (prefixWord ++ tailWord_5328462).sum := by decide
  have hdescent : baseEnd_5328462 < baseStart_5328462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328469 : List Nat := [1, 3, 2, 2, 1, 1, 1, 5, 1, 3, 3]
def baseStart_5328469 : Nat := 118140960795 + 5328469 * 2 ^ 59
def prefixEnd_5328469 : Nat := 4983230072969 + 3 ^ 40 * 5328469 * 2
def baseEnd_5328469 : Nat := 2736065749582218074232323

theorem tailTrace_5328469 : CollatzResearch.WordTrace tailWord_5328469 prefixEnd_5328469 2736065749582218074232323 := by
  unfold tailWord_5328469
  simp only [CollatzResearch.WordTrace]
  refine ⟨194345230532874317899116461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129563487021916211932744307 194345230532874317899116461)
  ·
    refine ⟨72879461449827869212168673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194345230532874317899116461 72879461449827869212168673)
    ·
      refine ⟨54659596087370901909126505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72879461449827869212168673 54659596087370901909126505)
      ·
        refine ⟨40994697065528176431844879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54659596087370901909126505 40994697065528176431844879)
        ·
          refine ⟨61492045598292264647767319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40994697065528176431844879 61492045598292264647767319)
          ·
            refine ⟨92238068397438396971650979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61492045598292264647767319 92238068397438396971650979)
            ·
              refine ⟨138357102596157595457476469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92238068397438396971650979 138357102596157595457476469)
              ·
                refine ⟨12970978368389774574138419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138357102596157595457476469 12970978368389774574138419)
                ·
                  refine ⟨19456467552584661861207629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12970978368389774574138419 19456467552584661861207629)
                  ·
                    refine ⟨7296175332219248197952861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19456467552584661861207629 7296175332219248197952861)
                    ·
                      refine ⟨2736065749582218074232323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7296175332219248197952861 2736065749582218074232323)
                      ·
                        rfl

theorem cell23_5328469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_5328469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328469 prefixEnd_5328469 := by exact prefixLift 5328469
  have htrace : WordTrace (prefixWord ++ tailWord_5328469) baseStart_5328469 baseEnd_5328469 := by
    simpa [prefixWord, tailWord_5328469, baseEnd_5328469] using wordTrace_append hprefix tailTrace_5328469
  have hstable : (prefixWord ++ tailWord_5328469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328469).length < 2 ^ (prefixWord ++ tailWord_5328469).sum := by decide
  have hdescent : baseEnd_5328469 < baseStart_5328469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328470 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_5328470 : Nat := 118140960795 + 5328470 * 2 ^ 59
def prefixEnd_5328470 : Nat := 4983230072969 + 3 ^ 40 * 5328470 * 2
def baseEnd_5328470 : Nat := 2736066263062872570319819

theorem tailTrace_5328470 : CollatzResearch.WordTrace tailWord_5328470 prefixEnd_5328470 2736066263062872570319819 := by
  unfold tailWord_5328470
  simp only [CollatzResearch.WordTrace]
  refine ⟨12146579187866918441868929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129563511337247130046601909 12146579187866918441868929)
  ·
    refine ⟨9109934390900188831401697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12146579187866918441868929 9109934390900188831401697)
    ·
      refine ⟨6832450793175141623551273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9109934390900188831401697 6832450793175141623551273)
      ·
        refine ⟨5124338094881356217663455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6832450793175141623551273 5124338094881356217663455)
        ·
          refine ⟨7686507142322034326495183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5124338094881356217663455 7686507142322034326495183)
          ·
            refine ⟨11529760713483051489742775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7686507142322034326495183 11529760713483051489742775)
            ·
              refine ⟨17294641070224577234614163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11529760713483051489742775 17294641070224577234614163)
              ·
                refine ⟨25941961605336865851921245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17294641070224577234614163 25941961605336865851921245)
                ·
                  refine ⟨9728235602001324694470467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25941961605336865851921245 9728235602001324694470467)
                  ·
                    refine ⟨14592353403001987041705701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9728235602001324694470467 14592353403001987041705701)
                    ·
                      refine ⟨2736066263062872570319819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14592353403001987041705701 2736066263062872570319819)
                      ·
                        rfl

theorem cell23_5328470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_5328470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328470 prefixEnd_5328470 := by exact prefixLift 5328470
  have htrace : WordTrace (prefixWord ++ tailWord_5328470) baseStart_5328470 baseEnd_5328470 := by
    simpa [prefixWord, tailWord_5328470, baseEnd_5328470] using wordTrace_append hprefix tailTrace_5328470
  have hstable : (prefixWord ++ tailWord_5328470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328470).length < 2 ^ (prefixWord ++ tailWord_5328470).sum := by decide
  have hdescent : baseEnd_5328470 < baseStart_5328470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328509 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_5328509 : Nat := 118140960795 + 5328509 * 2 ^ 59
def prefixEnd_5328509 : Nat := 4983230072969 + 3 ^ 40 * 5328509 * 2
def baseEnd_5328509 : Nat := 2736086288808397917732139

theorem tailTrace_5328509 : CollatzResearch.WordTrace tailWord_5328509 prefixEnd_5328509 2736086288808397917732139 := by
  unfold tailWord_5328509
  simp only [CollatzResearch.WordTrace]
  refine ⟨194346689452729404730572581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129564459635152936487048387 194346689452729404730572581)
  ·
    refine ⟨36440004272386763386982359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194346689452729404730572581 36440004272386763386982359)
    ·
      refine ⟨54660006408580145080473539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36440004272386763386982359 54660006408580145080473539)
      ·
        refine ⟨81990009612870217620710309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54660006408580145080473539 81990009612870217620710309)
        ·
          refine ⟨15373126802413165803883183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81990009612870217620710309 15373126802413165803883183)
          ·
            refine ⟨23059690203619748705824775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15373126802413165803883183 23059690203619748705824775)
            ·
              refine ⟨34589535305429623058737163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23059690203619748705824775 34589535305429623058737163)
              ·
                refine ⟨51884302958144434588105745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34589535305429623058737163 51884302958144434588105745)
                ·
                  refine ⟨38913227218608325941079309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51884302958144434588105745 38913227218608325941079309)
                  ·
                    refine ⟨14592460206978122227904741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38913227218608325941079309 14592460206978122227904741)
                    ·
                      refine ⟨2736086288808397917732139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14592460206978122227904741 2736086288808397917732139)
                      ·
                        rfl

theorem cell23_5328509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_5328509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328509 prefixEnd_5328509 := by exact prefixLift 5328509
  have htrace : WordTrace (prefixWord ++ tailWord_5328509) baseStart_5328509 baseEnd_5328509 := by
    simpa [prefixWord, tailWord_5328509, baseEnd_5328509] using wordTrace_append hprefix tailTrace_5328509
  have hstable : (prefixWord ++ tailWord_5328509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328509).length < 2 ^ (prefixWord ++ tailWord_5328509).sum := by decide
  have hdescent : baseEnd_5328509 < baseStart_5328509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328519 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 2, 6]
def baseStart_5328519 : Nat := 118140960795 + 5328519 * 2 ^ 59
def prefixEnd_5328519 : Nat := 4983230072969 + 3 ^ 40 * 5328519 * 2
def baseEnd_5328519 : Nat := 912030474538314292869031

theorem tailTrace_5328519 : CollatzResearch.WordTrace tailWord_5328519 prefixEnd_5328519 912030474538314292869031 := by
  unfold tailWord_5328519
  simp only [CollatzResearch.WordTrace]
  refine ⟨194347054182693176438436611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129564702788462117625624407 194347054182693176438436611)
  ·
    refine ⟨291520581274039764657654917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194347054182693176438436611 291520581274039764657654917)
    ·
      refine ⟨54660108988882455873310297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 291520581274039764657654917 54660108988882455873310297)
      ·
        refine ⟨40995081741661841904982723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54660108988882455873310297 40995081741661841904982723)
        ·
          refine ⟨61492622612492762857474085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40995081741661841904982723 61492622612492762857474085)
          ·
            refine ⟨11529866739842393035776391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61492622612492762857474085 11529866739842393035776391)
            ·
              refine ⟨17294800109763589553664587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11529866739842393035776391 17294800109763589553664587)
              ·
                refine ⟨25942200164645384330496881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17294800109763589553664587 25942200164645384330496881)
                ·
                  refine ⟨19456650123484038247872661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25942200164645384330496881 19456650123484038247872661)
                  ·
                    refine ⟨912030474538314292869031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19456650123484038247872661 912030474538314292869031)
                    ·
                      rfl

theorem cell23_5328519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_5328519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328519 prefixEnd_5328519 := by exact prefixLift 5328519
  have htrace : WordTrace (prefixWord ++ tailWord_5328519) baseStart_5328519 baseEnd_5328519 := by
    simpa [prefixWord, tailWord_5328519, baseEnd_5328519] using wordTrace_append hprefix tailTrace_5328519
  have hstable : (prefixWord ++ tailWord_5328519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328519).length < 2 ^ (prefixWord ++ tailWord_5328519).sum := by decide
  have hdescent : baseEnd_5328519 < baseStart_5328519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328559 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 3]
def baseStart_5328559 : Nat := 118140960795 + 5328559 * 2 ^ 59
def prefixEnd_5328559 : Nat := 4983230072969 + 3 ^ 40 * 5328559 * 2
def baseEnd_5328559 : Nat := 2736111962841122722106909

theorem tailTrace_5328559 : CollatzResearch.WordTrace tailWord_5328559 prefixEnd_5328559 2736111962841122722106909 := by
  unfold tailWord_5328559
  simp only [CollatzResearch.WordTrace]
  refine ⟨194348513102548263269892731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129565675401698842179928487 194348513102548263269892731)
  ·
    refine ⟨291522769653822394904839097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194348513102548263269892731 291522769653822394904839097)
    ·
      refine ⟨218642077240366796178629323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291522769653822394904839097 218642077240366796178629323)
      ·
        refine ⟨327963115860550194267943985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218642077240366796178629323 327963115860550194267943985)
        ·
          refine ⟨245972336895412645700957989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327963115860550194267943985 245972336895412645700957989)
          ·
            refine ⟨46119813167889871068929623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245972336895412645700957989 46119813167889871068929623)
            ·
              refine ⟨69179719751834806603394435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46119813167889871068929623 69179719751834806603394435)
              ·
                refine ⟨103769579627752209905091653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69179719751834806603394435 103769579627752209905091653)
                ·
                  refine ⟨19456796180203539357204685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103769579627752209905091653 19456796180203539357204685)
                  ·
                    refine ⟨7296298567576327258951757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19456796180203539357204685 7296298567576327258951757)
                    ·
                      refine ⟨2736111962841122722106909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7296298567576327258951757 2736111962841122722106909)
                      ·
                        rfl

theorem cell23_5328559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 3].length) (baseStart_5328559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328559 prefixEnd_5328559 := by exact prefixLift 5328559
  have htrace : WordTrace (prefixWord ++ tailWord_5328559) baseStart_5328559 baseEnd_5328559 := by
    simpa [prefixWord, tailWord_5328559, baseEnd_5328559] using wordTrace_append hprefix tailTrace_5328559
  have hstable : (prefixWord ++ tailWord_5328559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328559).length < 2 ^ (prefixWord ++ tailWord_5328559).sum := by decide
  have hdescent : baseEnd_5328559 < baseStart_5328559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328596 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_5328596 : Nat := 118140960795 + 5328596 * 2 ^ 59
def prefixEnd_5328596 : Nat := 4983230072969 + 3 ^ 40 * 5328596 * 2
def baseEnd_5328596 : Nat := 912043653875113025781413

theorem tailTrace_5328596 : CollatzResearch.WordTrace tailWord_5328596 prefixEnd_5328596 912043653875113025781413 := by
  unfold tailWord_5328596
  simp only [CollatzResearch.WordTrace]
  refine ⟨97174931301707109294494821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129566575068942812392659761 97174931301707109294494821)
  ·
    refine ⟨18220299619070082992717779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97174931301707109294494821 18220299619070082992717779)
    ·
      refine ⟨27330449428605124489076669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18220299619070082992717779 27330449428605124489076669)
      ·
        refine ⟨10248918535726921683403751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27330449428605124489076669 10248918535726921683403751)
        ·
          refine ⟨15373377803590382525105627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10248918535726921683403751 15373377803590382525105627)
          ·
            refine ⟨23060066705385573787658441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15373377803590382525105627 23060066705385573787658441)
            ·
              refine ⟨17295050029039180340743831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23060066705385573787658441 17295050029039180340743831)
              ·
                refine ⟨25942575043558770511115747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17295050029039180340743831 25942575043558770511115747)
                ·
                  refine ⟨38913862565338155766673621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25942575043558770511115747 38913862565338155766673621)
                  ·
                    refine ⟨912043653875113025781413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38913862565338155766673621 912043653875113025781413)
                    ·
                      rfl

theorem cell23_5328596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_5328596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328596 prefixEnd_5328596 := by exact prefixLift 5328596
  have htrace : WordTrace (prefixWord ++ tailWord_5328596) baseStart_5328596 baseEnd_5328596 := by
    simpa [prefixWord, tailWord_5328596, baseEnd_5328596] using wordTrace_append hprefix tailTrace_5328596
  have hstable : (prefixWord ++ tailWord_5328596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328596).length < 2 ^ (prefixWord ++ tailWord_5328596).sum := by decide
  have hdescent : baseEnd_5328596 < baseStart_5328596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328599 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 4]
def baseStart_5328599 : Nat := 118140960795 + 5328599 * 2 ^ 59
def prefixEnd_5328599 : Nat := 4983230072969 + 3 ^ 40 * 5328599 * 2
def baseEnd_5328599 : Nat := 2736132502067302565606725

theorem tailTrace_5328599 : CollatzResearch.WordTrace tailWord_5328599 prefixEnd_5328599 2736132502067302565606725 := by
  unfold tailWord_5328599
  simp only [CollatzResearch.WordTrace]
  refine ⟨194349972022403350101348851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129566648014935566734232567 194349972022403350101348851)
  ·
    refine ⟨291524958033605025152023277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194349972022403350101348851 291524958033605025152023277)
    ·
      refine ⟨109321859262601884432008729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291524958033605025152023277 109321859262601884432008729)
      ·
        refine ⟨81991394446951413324006547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109321859262601884432008729 81991394446951413324006547)
        ·
          refine ⟨122987091670427119986009821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81991394446951413324006547 122987091670427119986009821)
          ·
            refine ⟨46120159376410169994753683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122987091670427119986009821 46120159376410169994753683)
            ·
              refine ⟨69180239064615254992130525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46120159376410169994753683 69180239064615254992130525)
              ·
                refine ⟨25942589649230720622048947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69180239064615254992130525 25942589649230720622048947)
                ·
                  refine ⟨38913884473846080933073421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25942589649230720622048947 38913884473846080933073421)
                  ·
                    refine ⟨14592706677692280349902533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38913884473846080933073421 14592706677692280349902533)
                    ·
                      refine ⟨2736132502067302565606725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14592706677692280349902533 2736132502067302565606725)
                      ·
                        rfl

theorem cell23_5328599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_5328599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328599 prefixEnd_5328599 := by exact prefixLift 5328599
  have htrace : WordTrace (prefixWord ++ tailWord_5328599) baseStart_5328599 baseEnd_5328599 := by
    simpa [prefixWord, tailWord_5328599, baseEnd_5328599] using wordTrace_append hprefix tailTrace_5328599
  have hstable : (prefixWord ++ tailWord_5328599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328599).length < 2 ^ (prefixWord ++ tailWord_5328599).sum := by decide
  have hdescent : baseEnd_5328599 < baseStart_5328599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328616 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_5328616 : Nat := 118140960795 + 5328616 * 2 ^ 59
def prefixEnd_5328616 : Nat := 4983230072969 + 3 ^ 40 * 5328616 * 2
def baseEnd_5328616 : Nat := 2736141231238428999094147

theorem tailTrace_5328616 : CollatzResearch.WordTrace tailWord_5328616 prefixEnd_5328616 2736141231238428999094147 := by
  unfold tailWord_5328616
  simp only [CollatzResearch.WordTrace]
  refine ⟨97175296031670881002358851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129567061375561174669811801 97175296031670881002358851)
  ·
    refine ⟨145762944047506321503538277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97175296031670881002358851 145762944047506321503538277)
    ·
      refine ⟨27330552008907435281913427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145762944047506321503538277 27330552008907435281913427)
      ·
        refine ⟨40995828013361152922870141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27330552008907435281913427 40995828013361152922870141)
        ·
          refine ⟨15373435505010432346076303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40995828013361152922870141 15373435505010432346076303)
          ·
            refine ⟨23060153257515648519114455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15373435505010432346076303 23060153257515648519114455)
            ·
              refine ⟨34590229886273472778671683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23060153257515648519114455 34590229886273472778671683)
              ·
                refine ⟨51885344829410209168007525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34590229886273472778671683 51885344829410209168007525)
                ·
                  refine ⟨9728502155514414219001411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51885344829410209168007525 9728502155514414219001411)
                  ·
                    refine ⟨14592753233271621328502117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9728502155514414219001411 14592753233271621328502117)
                    ·
                      refine ⟨2736141231238428999094147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14592753233271621328502117 2736141231238428999094147)
                      ·
                        rfl

theorem cell23_5328616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_5328616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328616 prefixEnd_5328616 := by exact prefixLift 5328616
  have htrace : WordTrace (prefixWord ++ tailWord_5328616) baseStart_5328616 baseEnd_5328616 := by
    simpa [prefixWord, tailWord_5328616, baseEnd_5328616] using wordTrace_append hprefix tailTrace_5328616
  have hstable : (prefixWord ++ tailWord_5328616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328616).length < 2 ^ (prefixWord ++ tailWord_5328616).sum := by decide
  have hdescent : baseEnd_5328616 < baseStart_5328616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328636 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 4, 2, 3]
def baseStart_5328636 : Nat := 118140960795 + 5328636 * 2 ^ 59
def prefixEnd_5328636 : Nat := 4983230072969 + 3 ^ 40 * 5328636 * 2
def baseEnd_5328636 : Nat := 2736151500851518920844055

theorem tailTrace_5328636 : CollatzResearch.WordTrace tailWord_5328636 prefixEnd_5328636 2736151500851518920844055 := by
  unfold tailWord_5328636
  simp only [CollatzResearch.WordTrace]
  refine ⟨97175660761634652710222881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129567547682179536946963841 97175660761634652710222881)
  ·
    refine ⟨72881745571225989532667161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97175660761634652710222881 72881745571225989532667161)
    ·
      refine ⟨54661309178419492149500371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72881745571225989532667161 54661309178419492149500371)
      ·
        refine ⟨81991963767629238224250557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54661309178419492149500371 81991963767629238224250557)
        ·
          refine ⟨30746986412860964334093959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81991963767629238224250557 30746986412860964334093959)
          ·
            refine ⟨46120479619291446501140939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30746986412860964334093959 46120479619291446501140939)
            ·
              refine ⟨69180719428937169751711409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46120479619291446501140939 69180719428937169751711409)
              ·
                refine ⟨51885539571702877313783557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69180719428937169751711409 51885539571702877313783557)
                ·
                  refine ⟨9728538669694289496334417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51885539571702877313783557 9728538669694289496334417)
                  ·
                    refine ⟨7296404002270717122250813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9728538669694289496334417 7296404002270717122250813)
                    ·
                      refine ⟨2736151500851518920844055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7296404002270717122250813 2736151500851518920844055)
                      ·
                        rfl

theorem cell23_5328636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_5328636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328636 prefixEnd_5328636 := by exact prefixLift 5328636
  have htrace : WordTrace (prefixWord ++ tailWord_5328636) baseStart_5328636 baseEnd_5328636 := by
    simpa [prefixWord, tailWord_5328636, baseEnd_5328636] using wordTrace_append hprefix tailTrace_5328636
  have hstable : (prefixWord ++ tailWord_5328636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328636).length < 2 ^ (prefixWord ++ tailWord_5328636).sum := by decide
  have hdescent : baseEnd_5328636 < baseStart_5328636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328677 : List Nat := [1, 3, 1, 2, 3, 4, 2, 2, 1, 4]
def baseStart_5328677 : Nat := 118140960795 + 5328677 * 2 ^ 59
def prefixEnd_5328677 : Nat := 4983230072969 + 3 ^ 40 * 5328677 * 2
def baseEnd_5328677 : Nat := 912057517852784420143789

theorem tailTrace_5328677 : CollatzResearch.WordTrace tailWord_5328677 prefixEnd_5328677 912057517852784420143789 := by
  unfold tailWord_5328677
  simp only [CollatzResearch.WordTrace]
  refine ⟨194352816916120769422688285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129568544610747179615125523 194352816916120769422688285)
  ·
    refine ⟨72882306343545288533508107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194352816916120769422688285 72882306343545288533508107)
    ·
      refine ⟨109323459515317932800262161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72882306343545288533508107 109323459515317932800262161)
      ·
        refine ⟨81992594636488449600196621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109323459515317932800262161 81992594636488449600196621)
        ·
          refine ⟨30747222988683168600073733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81992594636488449600196621 30747222988683168600073733)
          ·
            refine ⟨5765104310378094112513825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30747222988683168600073733 5765104310378094112513825)
            ·
              refine ⟨4323828232783570584385369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5765104310378094112513825 4323828232783570584385369)
              ·
                refine ⟨3242871174587677938289027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4323828232783570584385369 3242871174587677938289027)
                ·
                  refine ⟨4864306761881516907433541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3242871174587677938289027 4864306761881516907433541)
                  ·
                    refine ⟨912057517852784420143789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4864306761881516907433541 912057517852784420143789)
                    ·
                      rfl

theorem cell23_5328677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 1, 4].length) (baseStart_5328677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328677 prefixEnd_5328677 := by exact prefixLift 5328677
  have htrace : WordTrace (prefixWord ++ tailWord_5328677) baseStart_5328677 baseEnd_5328677 := by
    simpa [prefixWord, tailWord_5328677, baseEnd_5328677] using wordTrace_append hprefix tailTrace_5328677
  have hstable : (prefixWord ++ tailWord_5328677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328677).length < 2 ^ (prefixWord ++ tailWord_5328677).sum := by decide
  have hdescent : baseEnd_5328677 < baseStart_5328677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328729 : List Nat := [1, 2, 1, 2, 2, 3, 12]
def baseStart_5328729 : Nat := 118140960795 + 5328729 * 2 ^ 59
def prefixEnd_5328729 : Nat := 4983230072969 + 3 ^ 40 * 5328729 * 2
def baseEnd_5328729 : Nat := 33780237710523296999767

theorem tailTrace_5328729 : CollatzResearch.WordTrace tailWord_5328729 prefixEnd_5328729 33780237710523296999767 := by
  unfold tailWord_5328729
  simp only [CollatzResearch.WordTrace]
  refine ⟨194354713511932382303581241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129569809007954921535720827 194354713511932382303581241)
  ·
    refine ⟨145766035133949286727685931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194354713511932382303581241 145766035133949286727685931)
    ·
      refine ⟨218649052700923930091528897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145766035133949286727685931 218649052700923930091528897)
      ·
        refine ⟨163986789525692947568646673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218649052700923930091528897 163986789525692947568646673)
        ·
          refine ⟨122990092144269710676485005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163986789525692947568646673 122990092144269710676485005)
          ·
            refine ⟨46121284554101141503681877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122990092144269710676485005 46121284554101141503681877)
            ·
              refine ⟨33780237710523296999767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 46121284554101141503681877 33780237710523296999767)
              ·
                rfl

theorem cell23_5328729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 12].length) (baseStart_5328729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328729 prefixEnd_5328729 := by exact prefixLift 5328729
  have htrace : WordTrace (prefixWord ++ tailWord_5328729) baseStart_5328729 baseEnd_5328729 := by
    simpa [prefixWord, tailWord_5328729, baseEnd_5328729] using wordTrace_append hprefix tailTrace_5328729
  have hstable : (prefixWord ++ tailWord_5328729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328729).length < 2 ^ (prefixWord ++ tailWord_5328729).sum := by decide
  have hdescent : baseEnd_5328729 < baseStart_5328729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328750 : List Nat := [4, 1, 2, 3, 1, 3, 1, 1, 1, 6]
def baseStart_5328750 : Nat := 118140960795 + 5328750 * 2 ^ 59
def prefixEnd_5328750 : Nat := 4983230072969 + 3 ^ 40 * 5328750 * 2
def baseEnd_5328750 : Nat := 912070012548710491606177

theorem tailTrace_5328750 : CollatzResearch.WordTrace tailWord_5328750 prefixEnd_5328750 912070012548710491606177 := by
  unfold tailWord_5328750
  simp only [CollatzResearch.WordTrace]
  refine ⟨24294434930607037861261963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129570319629904201926730469 24294434930607037861261963)
  ·
    refine ⟨36441652395910556791892945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24294434930607037861261963 36441652395910556791892945)
    ·
      refine ⟨27331239296932917593919709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36441652395910556791892945 27331239296932917593919709)
      ·
        refine ⟨10249214736349844097719891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27331239296932917593919709 10249214736349844097719891)
        ·
          refine ⟨15373822104524766146579837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10249214736349844097719891 15373822104524766146579837)
          ·
            refine ⟨5765183289196787304967439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15373822104524766146579837 5765183289196787304967439)
            ·
              refine ⟨8647774933795180957451159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5765183289196787304967439 8647774933795180957451159)
              ·
                refine ⟨12971662400692771436176739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8647774933795180957451159 12971662400692771436176739)
                ·
                  refine ⟨19457493601039157154265109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12971662400692771436176739 19457493601039157154265109)
                  ·
                    refine ⟨912070012548710491606177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19457493601039157154265109 912070012548710491606177)
                    ·
                      rfl

theorem cell23_5328750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_5328750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328750 prefixEnd_5328750 := by exact prefixLift 5328750
  have htrace : WordTrace (prefixWord ++ tailWord_5328750) baseStart_5328750 baseEnd_5328750 := by
    simpa [prefixWord, tailWord_5328750, baseEnd_5328750] using wordTrace_append hprefix tailTrace_5328750
  have hstable : (prefixWord ++ tailWord_5328750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328750).length < 2 ^ (prefixWord ++ tailWord_5328750).sum := by decide
  have hdescent : baseEnd_5328750 < baseStart_5328750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328773 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 6, 1, 3]
def baseStart_5328773 : Nat := 118140960795 + 5328773 * 2 ^ 59
def prefixEnd_5328773 : Nat := 4983230072969 + 3 ^ 40 * 5328773 * 2
def baseEnd_5328773 : Nat := 2736221847701184884830925

theorem tailTrace_5328773 : CollatzResearch.WordTrace tailWord_5328773 prefixEnd_5328773 2736221847701184884830925 := by
  unfold tailWord_5328773
  simp only [CollatzResearch.WordTrace]
  refine ⟨194356318323772977818182973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129570878882515318545455315 194356318323772977818182973)
  ·
    refine ⟨72883619371414866681818615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194356318323772977818182973 72883619371414866681818615)
    ·
      refine ⟨109325429057122300022727923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72883619371414866681818615 109325429057122300022727923)
      ·
        refine ⟨163988143585683450034091885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109325429057122300022727923 163988143585683450034091885)
        ·
          refine ⟨61495553844631293762784457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163988143585683450034091885 61495553844631293762784457)
          ·
            refine ⟨46121665383473470322088343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61495553844631293762784457 46121665383473470322088343)
            ·
              refine ⟨69182498075210205483132515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46121665383473470322088343 69182498075210205483132515)
              ·
                refine ⟨103773747112815308224698773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69182498075210205483132515 103773747112815308224698773)
                ·
                  refine ⟨4864394395913217573032755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103773747112815308224698773 4864394395913217573032755)
                  ·
                    refine ⟨7296591593869826359549133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4864394395913217573032755 7296591593869826359549133)
                    ·
                      refine ⟨2736221847701184884830925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7296591593869826359549133 2736221847701184884830925)
                      ·
                        rfl

theorem cell23_5328773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 1, 3].length) (baseStart_5328773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328773 prefixEnd_5328773 := by exact prefixLift 5328773
  have htrace : WordTrace (prefixWord ++ tailWord_5328773) baseStart_5328773 baseEnd_5328773 := by
    simpa [prefixWord, tailWord_5328773, baseEnd_5328773] using wordTrace_append hprefix tailTrace_5328773
  have hstable : (prefixWord ++ tailWord_5328773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328773).length < 2 ^ (prefixWord ++ tailWord_5328773).sum := by decide
  have hdescent : baseEnd_5328773 < baseStart_5328773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328807 : List Nat := [1, 1, 6, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_5328807 : Nat := 118140960795 + 5328807 * 2 ^ 59
def prefixEnd_5328807 : Nat := 4983230072969 + 3 ^ 40 * 5328807 * 2
def baseEnd_5328807 : Nat := 2736239306043437751805769

theorem tailTrace_5328807 : CollatzResearch.WordTrace tailWord_5328807 prefixEnd_5328807 2736239306043437751805769 := by
  unfold tailWord_5328807
  simp only [CollatzResearch.WordTrace]
  refine ⟨194357558405649801624920675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129571705603766534416613783 194357558405649801624920675)
  ·
    refine ⟨291536337608474702437381013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194357558405649801624920675 291536337608474702437381013)
    ·
      refine ⟨13665765825397251676752235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 291536337608474702437381013 13665765825397251676752235)
      ·
        refine ⟨20498648738095877515128353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13665765825397251676752235 20498648738095877515128353)
        ·
          refine ⟨15373986553571908136346265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20498648738095877515128353 15373986553571908136346265)
          ·
            refine ⟨11530489915178931102259699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15373986553571908136346265 11530489915178931102259699)
            ·
              refine ⟨17295734872768396653389549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11530489915178931102259699 17295734872768396653389549)
              ·
                refine ⟨6485900577288148745021081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17295734872768396653389549 6485900577288148745021081)
                ·
                  refine ⟨4864425432966111558765811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6485900577288148745021081 4864425432966111558765811)
                  ·
                    refine ⟨7296638149449167338148717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4864425432966111558765811 7296638149449167338148717)
                    ·
                      refine ⟨2736239306043437751805769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7296638149449167338148717 2736239306043437751805769)
                      ·
                        rfl

theorem cell23_5328807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_5328807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328807 prefixEnd_5328807 := by exact prefixLift 5328807
  have htrace : WordTrace (prefixWord ++ tailWord_5328807) baseStart_5328807 baseEnd_5328807 := by
    simpa [prefixWord, tailWord_5328807, baseEnd_5328807] using wordTrace_append hprefix tailTrace_5328807
  have hstable : (prefixWord ++ tailWord_5328807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328807).length < 2 ^ (prefixWord ++ tailWord_5328807).sum := by decide
  have hdescent : baseEnd_5328807 < baseStart_5328807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328817 : List Nat := [1, 2, 2, 4, 2, 1, 3, 2, 1, 3, 2]
def baseStart_5328817 : Nat := 118140960795 + 5328817 * 2 ^ 59
def prefixEnd_5328817 : Nat := 4983230072969 + 3 ^ 40 * 5328817 * 2
def baseEnd_5328817 : Nat := 2736244440849982712680723

theorem tailTrace_5328817 : CollatzResearch.WordTrace tailWord_5328817 prefixEnd_5328817 2736244440849982712680723 := by
  unfold tailWord_5328817
  simp only [CollatzResearch.WordTrace]
  refine ⟨194357923135613573332784705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129571948757075715555189803 194357923135613573332784705)
  ·
    refine ⟨145768442351710179999588529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194357923135613573332784705 145768442351710179999588529)
    ·
      refine ⟨109326331763782634999691397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145768442351710179999588529 109326331763782634999691397)
      ·
        refine ⟨20498687205709244062442137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109326331763782634999691397 20498687205709244062442137)
        ·
          refine ⟨15374015404281933046831603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20498687205709244062442137 15374015404281933046831603)
          ·
            refine ⟨23061023106422899570247405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15374015404281933046831603 23061023106422899570247405)
            ·
              refine ⟨8647883664908587338842777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23061023106422899570247405 8647883664908587338842777)
              ·
                refine ⟨6485912748681440504132083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8647883664908587338842777 6485912748681440504132083)
                ·
                  refine ⟨9728869123022160756198125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6485912748681440504132083 9728869123022160756198125)
                  ·
                    refine ⟨3648325921133310283574297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9728869123022160756198125 3648325921133310283574297)
                    ·
                      refine ⟨2736244440849982712680723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3648325921133310283574297 2736244440849982712680723)
                      ·
                        rfl

theorem cell23_5328817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_5328817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328817 prefixEnd_5328817 := by exact prefixLift 5328817
  have htrace : WordTrace (prefixWord ++ tailWord_5328817) baseStart_5328817 baseEnd_5328817 := by
    simpa [prefixWord, tailWord_5328817, baseEnd_5328817] using wordTrace_append hprefix tailTrace_5328817
  have hstable : (prefixWord ++ tailWord_5328817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328817).length < 2 ^ (prefixWord ++ tailWord_5328817).sum := by decide
  have hdescent : baseEnd_5328817 < baseStart_5328817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328826 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4]
def baseStart_5328826 : Nat := 118140960795 + 5328826 * 2 ^ 59
def prefixEnd_5328826 : Nat := 4983230072969 + 3 ^ 40 * 5328826 * 2
def baseEnd_5328826 : Nat := 2736249062175873177468181

theorem tailTrace_5328826 : CollatzResearch.WordTrace tailWord_5328826 prefixEnd_5328826 2736249062175873177468181 := by
  unfold tailWord_5328826
  simp only [CollatzResearch.WordTrace]
  refine ⟨48589562848145241967465583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129572167595053978579908221 48589562848145241967465583)
  ·
    refine ⟨72884344272217862951198375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48589562848145241967465583 72884344272217862951198375)
    ·
      refine ⟨109326516408326794426797563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72884344272217862951198375 109326516408326794426797563)
      ·
        refine ⟨163989774612490191640196345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109326516408326794426797563 163989774612490191640196345)
        ·
          refine ⟨122992330959367643730147259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163989774612490191640196345 122992330959367643730147259)
          ·
            refine ⟨184488496439051465595220889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122992330959367643730147259 184488496439051465595220889)
            ·
              refine ⟨138366372329288599196415667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184488496439051465595220889 138366372329288599196415667)
              ·
                refine ⟨207549558493932898794623501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138366372329288599196415667 207549558493932898794623501)
                ·
                  refine ⟨77831084435224837047983813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207549558493932898794623501 77831084435224837047983813)
                  ·
                    refine ⟨14593328331604656946496965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77831084435224837047983813 14593328331604656946496965)
                    ·
                      refine ⟨2736249062175873177468181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14593328331604656946496965 2736249062175873177468181)
                      ·
                        rfl

theorem cell23_5328826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_5328826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328826 prefixEnd_5328826 := by exact prefixLift 5328826
  have htrace : WordTrace (prefixWord ++ tailWord_5328826) baseStart_5328826 baseEnd_5328826 := by
    simpa [prefixWord, tailWord_5328826, baseEnd_5328826] using wordTrace_append hprefix tailTrace_5328826
  have hstable : (prefixWord ++ tailWord_5328826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328826).length < 2 ^ (prefixWord ++ tailWord_5328826).sum := by decide
  have hdescent : baseEnd_5328826 < baseStart_5328826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328830 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2]
def baseStart_5328830 : Nat := 118140960795 + 5328830 * 2 ^ 59
def prefixEnd_5328830 : Nat := 4983230072969 + 3 ^ 40 * 5328830 * 2
def baseEnd_5328830 : Nat := 2736251116098491161818163

theorem tailTrace_5328830 : CollatzResearch.WordTrace tailWord_5328830 prefixEnd_5328830 2736251116098491161818163 := by
  unfold tailWord_5328830
  simp only [CollatzResearch.WordTrace]
  refine ⟨24294799660570809569125993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129572264856377651035338629 24294799660570809569125993)
  ·
    refine ⟨18221099745428107176844495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24294799660570809569125993 18221099745428107176844495)
    ·
      refine ⟨27331649618142160765266743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18221099745428107176844495 27331649618142160765266743)
      ·
        refine ⟨40997474427213241147900115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27331649618142160765266743 40997474427213241147900115)
        ·
          refine ⟨61496211640819861721850173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40997474427213241147900115 61496211640819861721850173)
          ·
            refine ⟨23061079365307448145693815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61496211640819861721850173 23061079365307448145693815)
            ·
              refine ⟨34591619047961172218540723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23061079365307448145693815 34591619047961172218540723)
              ·
                refine ⟨51887428571941758327811085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34591619047961172218540723 51887428571941758327811085)
                ·
                  refine ⟨19457785714478159372929157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51887428571941758327811085 19457785714478159372929157)
                  ·
                    refine ⟨3648334821464654882424217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19457785714478159372929157 3648334821464654882424217)
                    ·
                      refine ⟨2736251116098491161818163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3648334821464654882424217 2736251116098491161818163)
                      ·
                        rfl

theorem cell23_5328830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_5328830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328830 prefixEnd_5328830 := by exact prefixLift 5328830
  have htrace : WordTrace (prefixWord ++ tailWord_5328830) baseStart_5328830 baseEnd_5328830 := by
    simpa [prefixWord, tailWord_5328830, baseEnd_5328830] using wordTrace_append hprefix tailTrace_5328830
  have hstable : (prefixWord ++ tailWord_5328830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328830).length < 2 ^ (prefixWord ++ tailWord_5328830).sum := by decide
  have hdescent : baseEnd_5328830 < baseStart_5328830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328847 : List Nat := [1, 1, 2, 1, 1, 5, 4, 2, 2, 2, 2]
def baseStart_5328847 : Nat := 118140960795 + 5328847 * 2 ^ 59
def prefixEnd_5328847 : Nat := 4983230072969 + 3 ^ 40 * 5328847 * 2
def baseEnd_5328847 : Nat := 2736259845269617595305585

theorem tailTrace_5328847 : CollatzResearch.WordTrace tailWord_5328847 prefixEnd_5328847 2736259845269617595305585 := by
  unfold tailWord_5328847
  simp only [CollatzResearch.WordTrace]
  refine ⟨194359017325504888456376795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129572678217003258970917863 194359017325504888456376795)
  ·
    refine ⟨291538525988257332684565193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194359017325504888456376795 291538525988257332684565193)
    ·
      refine ⟨218653894491192999513423895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291538525988257332684565193 218653894491192999513423895)
      ·
        refine ⟨327980841736789499270135843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218653894491192999513423895 327980841736789499270135843)
        ·
          refine ⟨491971262605184248905203765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327980841736789499270135843 491971262605184248905203765)
          ·
            refine ⟨46122305869236023334862853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 491971262605184248905203765 46122305869236023334862853)
            ·
              refine ⟨8647932350481754375286785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46122305869236023334862853 8647932350481754375286785)
              ·
                refine ⟨6485949262861315781465089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8647932350481754375286785 6485949262861315781465089)
                ·
                  refine ⟨4864461947145986836098817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6485949262861315781465089 4864461947145986836098817)
                  ·
                    refine ⟨3648346460359490127074113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4864461947145986836098817 3648346460359490127074113)
                    ·
                      refine ⟨2736259845269617595305585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3648346460359490127074113 2736259845269617595305585)
                      ·
                        rfl

theorem cell23_5328847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 2, 2].length) (baseStart_5328847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328847 prefixEnd_5328847 := by exact prefixLift 5328847
  have htrace : WordTrace (prefixWord ++ tailWord_5328847) baseStart_5328847 baseEnd_5328847 := by
    simpa [prefixWord, tailWord_5328847, baseEnd_5328847] using wordTrace_append hprefix tailTrace_5328847
  have hstable : (prefixWord ++ tailWord_5328847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328847).length < 2 ^ (prefixWord ++ tailWord_5328847).sum := by decide
  have hdescent : baseEnd_5328847 < baseStart_5328847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328863 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 3]
def baseStart_5328863 : Nat := 118140960795 + 5328863 * 2 ^ 59
def prefixEnd_5328863 : Nat := 4983230072969 + 3 ^ 40 * 5328863 * 2
def baseEnd_5328863 : Nat := 2736268060960089532705511

theorem tailTrace_5328863 : CollatzResearch.WordTrace tailWord_5328863 prefixEnd_5328863 2736268060960089532705511 := by
  unfold tailWord_5328863
  simp only [CollatzResearch.WordTrace]
  refine ⟨194359600893446923188959243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129573067262297948792639495 194359600893446923188959243)
  ·
    refine ⟨291539401340170384783438865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194359600893446923188959243 291539401340170384783438865)
    ·
      refine ⟨218654551005127788587579149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291539401340170384783438865 218654551005127788587579149)
      ·
        refine ⟨81995456626922920720342181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218654551005127788587579149 81995456626922920720342181)
        ·
          refine ⟨15374148117548047635064159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81995456626922920720342181 15374148117548047635064159)
          ·
            refine ⟨23061222176322071452596239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15374148117548047635064159 23061222176322071452596239)
            ·
              refine ⟨34591833264483107178894359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23061222176322071452596239 34591833264483107178894359)
              ·
                refine ⟨51887749896724660768341539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34591833264483107178894359 51887749896724660768341539)
                ·
                  refine ⟨77831624845086991152512309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51887749896724660768341539 77831624845086991152512309)
                  ·
                    refine ⟨7296714829226905420548029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77831624845086991152512309 7296714829226905420548029)
                    ·
                      refine ⟨2736268060960089532705511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7296714829226905420548029 2736268060960089532705511)
                      ·
                        rfl

theorem cell23_5328863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_5328863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328863 prefixEnd_5328863 := by exact prefixLift 5328863
  have htrace : WordTrace (prefixWord ++ tailWord_5328863) baseStart_5328863 baseEnd_5328863 := by
    simpa [prefixWord, tailWord_5328863, baseEnd_5328863] using wordTrace_append hprefix tailTrace_5328863
  have hstable : (prefixWord ++ tailWord_5328863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328863).length < 2 ^ (prefixWord ++ tailWord_5328863).sum := by decide
  have hdescent : baseEnd_5328863 < baseStart_5328863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328876 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 7]
def baseStart_5328876 : Nat := 118140960795 + 5328876 * 2 ^ 59
def prefixEnd_5328876 : Nat := 4983230072969 + 3 ^ 40 * 5328876 * 2
def baseEnd_5328876 : Nat := 2736274736208597981842951

theorem tailTrace_5328876 : CollatzResearch.WordTrace tailWord_5328876 prefixEnd_5328876 2736274736208597981842951 := by
  unfold tailWord_5328876
  simp only [CollatzResearch.WordTrace]
  refine ⟨97180037521199913204591241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129573383361599884272788321 97180037521199913204591241)
  ·
    refine ⟨72885028140899934903443431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97180037521199913204591241 72885028140899934903443431)
    ·
      refine ⟨109327542211349902355165147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72885028140899934903443431 109327542211349902355165147)
      ·
        refine ⟨163991313317024853532747721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109327542211349902355165147 163991313317024853532747721)
        ·
          refine ⟨122993484987768640149560791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163991313317024853532747721 122993484987768640149560791)
          ·
            refine ⟨184490227481652960224341187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122993484987768640149560791 184490227481652960224341187)
            ·
              refine ⟨276735341222479440336511781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184490227481652960224341187 276735341222479440336511781)
              ·
                refine ⟨51887876479214895063095959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 276735341222479440336511781 51887876479214895063095959)
                ·
                  refine ⟨77831814718822342594643939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51887876479214895063095959 77831814718822342594643939)
                  ·
                    refine ⟨116747722078233513891965909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77831814718822342594643939 116747722078233513891965909)
                    ·
                      refine ⟨2736274736208597981842951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116747722078233513891965909 2736274736208597981842951)
                      ·
                        rfl

theorem cell23_5328876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_5328876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328876 prefixEnd_5328876 := by exact prefixLift 5328876
  have htrace : WordTrace (prefixWord ++ tailWord_5328876) baseStart_5328876 baseEnd_5328876 := by
    simpa [prefixWord, tailWord_5328876, baseEnd_5328876] using wordTrace_append hprefix tailTrace_5328876
  have hstable : (prefixWord ++ tailWord_5328876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328876).length < 2 ^ (prefixWord ++ tailWord_5328876).sum := by decide
  have hdescent : baseEnd_5328876 < baseStart_5328876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328920 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 2, 4, 2]
def baseStart_5328920 : Nat := 118140960795 + 5328920 * 2 ^ 59
def prefixEnd_5328920 : Nat := 4983230072969 + 3 ^ 40 * 5328920 * 2
def baseEnd_5328920 : Nat := 2736297329357395809692749

theorem tailTrace_5328920 : CollatzResearch.WordTrace tailWord_5328920 prefixEnd_5328920 2736297329357395809692749 := by
  unfold tailWord_5328920
  simp only [CollatzResearch.WordTrace]
  refine ⟨97180839927120210961892107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129574453236160281282522809 97180839927120210961892107)
  ·
    refine ⟨145771259890680316442838161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97180839927120210961892107 145771259890680316442838161)
    ·
      refine ⟨109328444918010237332128621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145771259890680316442838161 109328444918010237332128621)
      ·
        refine ⟨40998166844253838999548233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109328444918010237332128621 40998166844253838999548233)
        ·
          refine ⟨30748625133190379249661175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40998166844253838999548233 30748625133190379249661175)
          ·
            refine ⟨46122937699785568874491763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30748625133190379249661175 46122937699785568874491763)
            ·
              refine ⟨69184406549678353311737645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46122937699785568874491763 69184406549678353311737645)
              ·
                refine ⟨25944152456129382491901617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69184406549678353311737645 25944152456129382491901617)
                ·
                  refine ⟨19458114342097036868926213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25944152456129382491901617 19458114342097036868926213)
                  ·
                    refine ⟨3648396439143194412923665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19458114342097036868926213 3648396439143194412923665)
                    ·
                      refine ⟨2736297329357395809692749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3648396439143194412923665 2736297329357395809692749)
                      ·
                        rfl

theorem cell23_5328920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_5328920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328920 prefixEnd_5328920 := by exact prefixLift 5328920
  have htrace : WordTrace (prefixWord ++ tailWord_5328920) baseStart_5328920 baseEnd_5328920 := by
    simpa [prefixWord, tailWord_5328920, baseEnd_5328920] using wordTrace_append hprefix tailTrace_5328920
  have hstable : (prefixWord ++ tailWord_5328920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328920).length < 2 ^ (prefixWord ++ tailWord_5328920).sum := by decide
  have hdescent : baseEnd_5328920 < baseStart_5328920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328923 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 3]
def baseStart_5328923 : Nat := 118140960795 + 5328923 * 2 ^ 59
def prefixEnd_5328923 : Nat := 4983230072969 + 3 ^ 40 * 5328923 * 2
def baseEnd_5328923 : Nat := 2736298869799359297955235

theorem tailTrace_5328923 : CollatzResearch.WordTrace tailWord_5328923 prefixEnd_5328923 2736298869799359297955235 := by
  unfold tailWord_5328923
  simp only [CollatzResearch.WordTrace]
  refine ⟨194361789273229553436143423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129574526182153035624095615 194361789273229553436143423)
  ·
    refine ⟨291542683909844330154215135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194361789273229553436143423 291542683909844330154215135)
    ·
      refine ⟨437314025864766495231322703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291542683909844330154215135 437314025864766495231322703)
      ·
        refine ⟨655971038797149742846984055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437314025864766495231322703 655971038797149742846984055)
        ·
          refine ⟨983956558195724614270476083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655971038797149742846984055 983956558195724614270476083)
          ·
            refine ⟨1475934837293586921405714125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983956558195724614270476083 1475934837293586921405714125)
            ·
              refine ⟨553475563985095095527142797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1475934837293586921405714125 553475563985095095527142797)
              ·
                refine ⟨207553336494410660822678549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 553475563985095095527142797 207553336494410660822678549)
                ·
                  refine ⟨9729062648175499726063057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 207553336494410660822678549 9729062648175499726063057)
                  ·
                    refine ⟨7296796986131624794547293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9729062648175499726063057 7296796986131624794547293)
                    ·
                      refine ⟨2736298869799359297955235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7296796986131624794547293 2736298869799359297955235)
                      ·
                        rfl

theorem cell23_5328923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 3].length) (baseStart_5328923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328923 prefixEnd_5328923 := by exact prefixLift 5328923
  have htrace : WordTrace (prefixWord ++ tailWord_5328923) baseStart_5328923 baseEnd_5328923 := by
    simpa [prefixWord, tailWord_5328923, baseEnd_5328923] using wordTrace_append hprefix tailTrace_5328923
  have hstable : (prefixWord ++ tailWord_5328923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328923).length < 2 ^ (prefixWord ++ tailWord_5328923).sum := by decide
  have hdescent : baseEnd_5328923 < baseStart_5328923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328930 : List Nat := [3, 3, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_5328930 : Nat := 118140960795 + 5328930 * 2 ^ 59
def prefixEnd_5328930 : Nat := 4983230072969 + 3 ^ 40 * 5328930 * 2
def baseEnd_5328930 : Nat := 912100821387980256855901

theorem tailTrace_5328930 : CollatzResearch.WordTrace tailWord_5328930 prefixEnd_5328930 912100821387980256855901 := by
  unfold tailWord_5328930
  simp only [CollatzResearch.WordTrace]
  refine ⟨48590511146051048407912061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129574696389469462421098829 48590511146051048407912061)
  ·
    refine ⟨18221441679769143152967023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48590511146051048407912061 18221441679769143152967023)
    ·
      refine ⟨27332162519653714729450535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18221441679769143152967023 27332162519653714729450535)
      ·
        refine ⟨40998243779480572094175803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27332162519653714729450535 40998243779480572094175803)
        ·
          refine ⟨61497365669220858141263705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40998243779480572094175803 61497365669220858141263705)
          ·
            refine ⟨46123024251915643605947779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61497365669220858141263705 46123024251915643605947779)
            ·
              refine ⟨69184536377873465408921669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46123024251915643605947779 69184536377873465408921669)
              ·
                refine ⟨12972100570851274764172813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69184536377873465408921669 12972100570851274764172813)
                ·
                  refine ⟨4864537714069228036564805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12972100570851274764172813 4864537714069228036564805)
                  ·
                    refine ⟨912100821387980256855901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4864537714069228036564805 912100821387980256855901)
                    ·
                      rfl

theorem cell23_5328930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_5328930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328930 prefixEnd_5328930 := by exact prefixLift 5328930
  have htrace : WordTrace (prefixWord ++ tailWord_5328930) baseStart_5328930 baseEnd_5328930 := by
    simpa [prefixWord, tailWord_5328930, baseEnd_5328930] using wordTrace_append hprefix tailTrace_5328930
  have hstable : (prefixWord ++ tailWord_5328930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328930).length < 2 ^ (prefixWord ++ tailWord_5328930).sum := by decide
  have hdescent : baseEnd_5328930 < baseStart_5328930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328947 : List Nat := [1, 1, 1, 2, 4, 1, 5, 3, 1, 4]
def baseStart_5328947 : Nat := 118140960795 + 5328947 * 2 ^ 59
def prefixEnd_5328947 : Nat := 4983230072969 + 3 ^ 40 * 5328947 * 2
def baseEnd_5328947 : Nat := 912103731111689068018375

theorem tailTrace_5328947 : CollatzResearch.WordTrace tailWord_5328947 prefixEnd_5328947 912103731111689068018375 := by
  unfold tailWord_5328947
  simp only [CollatzResearch.WordTrace]
  refine ⟨194362664625142605535017095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129575109750095070356678063 194362664625142605535017095)
  ·
    refine ⟨291543996937713908302525643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194362664625142605535017095 291543996937713908302525643)
    ·
      refine ⟨437315995406570862453788465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291543996937713908302525643 437315995406570862453788465)
      ·
        refine ⟨327986996554928146840341349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437315995406570862453788465 327986996554928146840341349)
        ·
          refine ⟨61497561854049027532564003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 327986996554928146840341349 61497561854049027532564003)
          ·
            refine ⟨92246342781073541298846005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61497561854049027532564003 92246342781073541298846005)
            ·
              refine ⟨8648094635725644496766813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92246342781073541298846005 8648094635725644496766813)
              ·
                refine ⟨3243035488397116686287555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8648094635725644496766813 3243035488397116686287555)
                ·
                  refine ⟨4864553232595675029431333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3243035488397116686287555 4864553232595675029431333)
                  ·
                    refine ⟨912103731111689068018375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4864553232595675029431333 912103731111689068018375)
                    ·
                      rfl

theorem cell23_5328947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 1, 4].length) (baseStart_5328947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328947 prefixEnd_5328947 := by exact prefixLift 5328947
  have htrace : WordTrace (prefixWord ++ tailWord_5328947) baseStart_5328947 baseEnd_5328947 := by
    simpa [prefixWord, tailWord_5328947, baseEnd_5328947] using wordTrace_append hprefix tailTrace_5328947
  have hstable : (prefixWord ++ tailWord_5328947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328947).length < 2 ^ (prefixWord ++ tailWord_5328947).sum := by decide
  have hdescent : baseEnd_5328947 < baseStart_5328947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5328997 : List Nat := [1, 3, 1, 3, 2, 2, 1, 3, 2, 3, 2]
def baseStart_5328997 : Nat := 118140960795 + 5328997 * 2 ^ 59
def prefixEnd_5328997 : Nat := 4983230072969 + 3 ^ 40 * 5328997 * 2
def baseEnd_5328997 : Nat := 2736336867367792008429895

theorem tailTrace_5328997 : CollatzResearch.WordTrace tailWord_5328997 prefixEnd_5328997 2736336867367792008429895 := by
  unfold tailWord_5328997
  simp only [CollatzResearch.WordTrace]
  refine ⟨194364488274961464074337245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129576325516640976049558163 194364488274961464074337245)
  ·
    refine ⟨72886683103110549027876467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194364488274961464074337245 72886683103110549027876467)
    ·
      refine ⟨109330024654665823541814701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72886683103110549027876467 109330024654665823541814701)
      ·
        refine ⟨40998759245499683828180513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109330024654665823541814701 40998759245499683828180513)
        ·
          refine ⟨30749069434124762871135385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40998759245499683828180513 30749069434124762871135385)
          ·
            refine ⟨23061802075593572153351539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30749069434124762871135385 23061802075593572153351539)
            ·
              refine ⟨34592703113390358230027309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23061802075593572153351539 34592703113390358230027309)
              ·
                refine ⟨12972263667521384336260241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34592703113390358230027309 12972263667521384336260241)
                ·
                  refine ⟨9729197750641038252195181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12972263667521384336260241 9729197750641038252195181)
                  ·
                    refine ⟨3648449156490389344573193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9729197750641038252195181 3648449156490389344573193)
                    ·
                      refine ⟨2736336867367792008429895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3648449156490389344573193 2736336867367792008429895)
                      ·
                        rfl

theorem cell23_5328997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_5328997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5328997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5328997 prefixEnd_5328997 := by exact prefixLift 5328997
  have htrace : WordTrace (prefixWord ++ tailWord_5328997) baseStart_5328997 baseEnd_5328997 := by
    simpa [prefixWord, tailWord_5328997, baseEnd_5328997] using wordTrace_append hprefix tailTrace_5328997
  have hstable : (prefixWord ++ tailWord_5328997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5328997).length < 2 ^ (prefixWord ++ tailWord_5328997).sum := by decide
  have hdescent : baseEnd_5328997 < baseStart_5328997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5328997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329007 : List Nat := [1, 1, 2, 1, 3, 5, 3, 1, 1, 5]
def baseStart_5329007 : Nat := 118140960795 + 5329007 * 2 ^ 59
def prefixEnd_5329007 : Nat := 4983230072969 + 3 ^ 40 * 5329007 * 2
def baseEnd_5329007 : Nat := 912114000724778989768283

theorem tailTrace_5329007 : CollatzResearch.WordTrace tailWord_5329007 prefixEnd_5329007 912114000724778989768283 := by
  unfold tailWord_5329007
  simp only [CollatzResearch.WordTrace]
  refine ⟨194364853004925235782201275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129576568669950157188134183 194364853004925235782201275)
  ·
    refine ⟨291547279507387853673301913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194364853004925235782201275 291547279507387853673301913)
    ·
      refine ⟨218660459630540890254976435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291547279507387853673301913 218660459630540890254976435)
      ·
        refine ⟨327990689445811335382464653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218660459630540890254976435 327990689445811335382464653)
        ·
          refine ⟨122996508542179250768424245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 327990689445811335382464653 122996508542179250768424245)
          ·
            refine ⟨11530922675829304759539773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122996508542179250768424245 11530922675829304759539773)
            ·
              refine ⟨4324096003435989284827415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11530922675829304759539773 4324096003435989284827415)
              ·
                refine ⟨6486144005153983927241123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4324096003435989284827415 6486144005153983927241123)
                ·
                  refine ⟨9729216007730975890861685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6486144005153983927241123 9729216007730975890861685)
                  ·
                    refine ⟨912114000724778989768283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9729216007730975890861685 912114000724778989768283)
                    ·
                      rfl

theorem cell23_5329007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 1, 5].length) (baseStart_5329007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329007 prefixEnd_5329007 := by exact prefixLift 5329007
  have htrace : WordTrace (prefixWord ++ tailWord_5329007) baseStart_5329007 baseEnd_5329007 := by
    simpa [prefixWord, tailWord_5329007, baseEnd_5329007] using wordTrace_append hprefix tailTrace_5329007
  have hstable : (prefixWord ++ tailWord_5329007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329007).length < 2 ^ (prefixWord ++ tailWord_5329007).sum := by decide
  have hdescent : baseEnd_5329007 < baseStart_5329007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329014 : List Nat := [5, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2]
def baseStart_5329014 : Nat := 118140960795 + 5329014 * 2 ^ 59
def prefixEnd_5329014 : Nat := 4983230072969 + 3 ^ 40 * 5329014 * 2
def baseEnd_5329014 : Nat := 2736345596538918441917317

theorem tailTrace_5329014 : CollatzResearch.WordTrace tailWord_5329014 prefixEnd_5329014 2736345596538918441917317 := by
  unfold tailWord_5329014
  simp only [CollatzResearch.WordTrace]
  refine ⟨12147819269743742248606631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129576738877266583985137397 12147819269743742248606631)
  ·
    refine ⟨18221728904615613372909947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12147819269743742248606631 18221728904615613372909947)
    ·
      refine ⟨27332593356923420059364921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18221728904615613372909947 27332593356923420059364921)
      ·
        refine ⟨20499445017692565044523691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27332593356923420059364921 20499445017692565044523691)
        ·
          refine ⟨30749167526538847566785537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20499445017692565044523691 30749167526538847566785537)
          ·
            refine ⟨23061875644904135675089153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30749167526538847566785537 23061875644904135675089153)
            ·
              refine ⟨17296406733678101756316865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23061875644904135675089153 17296406733678101756316865)
              ·
                refine ⟨12972305050258576317237649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17296406733678101756316865 12972305050258576317237649)
                ·
                  refine ⟨9729228787693932237928237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12972305050258576317237649 9729228787693932237928237)
                  ·
                    refine ⟨3648460795385224589223089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9729228787693932237928237 3648460795385224589223089)
                    ·
                      refine ⟨2736345596538918441917317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3648460795385224589223089 2736345596538918441917317)
                      ·
                        rfl

theorem cell23_5329014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_5329014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329014 prefixEnd_5329014 := by exact prefixLift 5329014
  have htrace : WordTrace (prefixWord ++ tailWord_5329014) baseStart_5329014 baseEnd_5329014 := by
    simpa [prefixWord, tailWord_5329014, baseEnd_5329014] using wordTrace_append hprefix tailTrace_5329014
  have hstable : (prefixWord ++ tailWord_5329014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329014).length < 2 ^ (prefixWord ++ tailWord_5329014).sum := by decide
  have hdescent : baseEnd_5329014 < baseStart_5329014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329021 : List Nat := [1, 4, 1, 1, 3, 2, 4, 2, 1, 1, 3]
def baseStart_5329021 : Nat := 118140960795 + 5329021 * 2 ^ 59
def prefixEnd_5329021 : Nat := 4983230072969 + 3 ^ 40 * 5329021 * 2
def baseEnd_5329021 : Nat := 2736349190903499914529785

theorem tailTrace_5329021 : CollatzResearch.WordTrace tailWord_5329021 prefixEnd_5329021 2736349190903499914529785 := by
  unfold tailWord_5329021
  simp only [CollatzResearch.WordTrace]
  refine ⟨194365363626874516173210917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129576909084583010782140611 194365363626874516173210917)
  ·
    refine ⟨36443505680038971782477047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194365363626874516173210917 36443505680038971782477047)
    ·
      refine ⟨54665258520058457673715571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36443505680038971782477047 54665258520058457673715571)
      ·
        refine ⟨81997887780087686510573357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54665258520058457673715571 81997887780087686510573357)
        ·
          refine ⟨30749207917532882441465009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81997887780087686510573357 30749207917532882441465009)
          ·
            refine ⟨23061905938149661831098757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30749207917532882441465009 23061905938149661831098757)
            ·
              refine ⟨4324107363403061593331017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23061905938149661831098757 4324107363403061593331017)
              ·
                refine ⟨3243080522552296194998263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4324107363403061593331017 3243080522552296194998263)
                ·
                  refine ⟨4864620783828444292497395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3243080522552296194998263 4864620783828444292497395)
                  ·
                    refine ⟨7296931175742666438746093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4864620783828444292497395 7296931175742666438746093)
                    ·
                      refine ⟨2736349190903499914529785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7296931175742666438746093 2736349190903499914529785)
                      ·
                        rfl

theorem cell23_5329021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_5329021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329021 prefixEnd_5329021 := by exact prefixLift 5329021
  have htrace : WordTrace (prefixWord ++ tailWord_5329021) baseStart_5329021 baseEnd_5329021 := by
    simpa [prefixWord, tailWord_5329021, baseEnd_5329021] using wordTrace_append hprefix tailTrace_5329021
  have hstable : (prefixWord ++ tailWord_5329021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329021).length < 2 ^ (prefixWord ++ tailWord_5329021).sum := by decide
  have hdescent : baseEnd_5329021 < baseStart_5329021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329040 : List Nat := [2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 4]
def baseStart_5329040 : Nat := 118140960795 + 5329040 * 2 ^ 59
def prefixEnd_5329040 : Nat := 4983230072969 + 3 ^ 40 * 5329040 * 2
def baseEnd_5329040 : Nat := 2736358947035935340192197

theorem tailTrace_5329040 : CollatzResearch.WordTrace tailWord_5329040 prefixEnd_5329040 2736358947035935340192197 := by
  unfold tailWord_5329040
  simp only [CollatzResearch.WordTrace]
  refine ⟨97183028306902841209076287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129577371075870454945435049 97183028306902841209076287)
  ·
    refine ⟨145774542460354261813614431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97183028306902841209076287 145774542460354261813614431)
    ·
      refine ⟨218661813690531392720421647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145774542460354261813614431 218661813690531392720421647)
      ·
        refine ⟨327992720535797089080632471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218661813690531392720421647 327992720535797089080632471)
        ·
          refine ⟨491989080803695633620948707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327992720535797089080632471 491989080803695633620948707)
          ·
            refine ⟨737983621205543450431423061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491989080803695633620948707 737983621205543450431423061)
            ·
              refine ⟨8648245561002462309743239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 737983621205543450431423061 8648245561002462309743239)
              ·
                refine ⟨12972368341503693464614859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8648245561002462309743239 12972368341503693464614859)
                ·
                  refine ⟨19458552512255540196922289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12972368341503693464614859 19458552512255540196922289)
                  ·
                    refine ⟨14593914384191655147691717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19458552512255540196922289 14593914384191655147691717)
                    ·
                      refine ⟨2736358947035935340192197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14593914384191655147691717 2736358947035935340192197)
                      ·
                        rfl

theorem cell23_5329040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 4].length) (baseStart_5329040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329040 prefixEnd_5329040 := by exact prefixLift 5329040
  have htrace : WordTrace (prefixWord ++ tailWord_5329040) baseStart_5329040 baseEnd_5329040 := by
    simpa [prefixWord, tailWord_5329040, baseEnd_5329040] using wordTrace_append hprefix tailTrace_5329040
  have hstable : (prefixWord ++ tailWord_5329040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329040).length < 2 ^ (prefixWord ++ tailWord_5329040).sum := by decide
  have hdescent : baseEnd_5329040 < baseStart_5329040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329061 : List Nat := [1, 3, 1, 2, 1, 3, 4, 3, 1, 2, 2]
def baseStart_5329061 : Nat := 118140960795 + 5329061 * 2 ^ 59
def prefixEnd_5329061 : Nat := 4983230072969 + 3 ^ 40 * 5329061 * 2
def baseEnd_5329061 : Nat := 2736369730129679758029601

theorem tailTrace_5329061 : CollatzResearch.WordTrace tailWord_5329061 prefixEnd_5329061 2736369730129679758029601 := by
  unfold tailWord_5329061
  simp only [CollatzResearch.WordTrace]
  refine ⟨194366822546729603004667037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129577881697819735336444691 194366822546729603004667037)
  ·
    refine ⟨72887558455023601126750139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194366822546729603004667037 72887558455023601126750139)
    ·
      refine ⟨109331337682535401690125209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72887558455023601126750139 109331337682535401690125209)
      ·
        refine ⟨81998503261901551267593907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109331337682535401690125209 81998503261901551267593907)
        ·
          refine ⟨122997754892852326901390861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81998503261901551267593907 122997754892852326901390861)
          ·
            refine ⟨46124158084819622588021573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122997754892852326901390861 46124158084819622588021573)
            ·
              refine ⟨8648279640903679235254045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46124158084819622588021573 8648279640903679235254045)
              ·
                refine ⟨3243104865338879713220267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8648279640903679235254045 3243104865338879713220267)
                ·
                  refine ⟨4864657298008319569830401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3243104865338879713220267 4864657298008319569830401)
                  ·
                    refine ⟨3648492973506239677372801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4864657298008319569830401 3648492973506239677372801)
                    ·
                      refine ⟨2736369730129679758029601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3648492973506239677372801 2736369730129679758029601)
                      ·
                        rfl

theorem cell23_5329061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_5329061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329061 prefixEnd_5329061 := by exact prefixLift 5329061
  have htrace : WordTrace (prefixWord ++ tailWord_5329061) baseStart_5329061 baseEnd_5329061 := by
    simpa [prefixWord, tailWord_5329061, baseEnd_5329061] using wordTrace_append hprefix tailTrace_5329061
  have hstable : (prefixWord ++ tailWord_5329061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329061).length < 2 ^ (prefixWord ++ tailWord_5329061).sum := by decide
  have hdescent : baseEnd_5329061 < baseStart_5329061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329120 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 5]
def baseStart_5329120 : Nat := 118140960795 + 5329120 * 2 ^ 59
def prefixEnd_5329120 : Nat := 4983230072969 + 3 ^ 40 * 5329120 * 2
def baseEnd_5329120 : Nat := 2736400025488295027191829

theorem tailTrace_5329120 : CollatzResearch.WordTrace tailWord_5329120 prefixEnd_5329120 2736400025488295027191829 := by
  unfold tailWord_5329120
  simp only [CollatzResearch.WordTrace]
  refine ⟨97184487226757928040532407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129579316302343904054043209 97184487226757928040532407)
  ·
    refine ⟨145776730840136892060798611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97184487226757928040532407 145776730840136892060798611)
    ·
      refine ⟨218665096260205338091197917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145776730840136892060798611 218665096260205338091197917)
      ·
        refine ⟨81999411097577001784199219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218665096260205338091197917 81999411097577001784199219)
        ·
          refine ⟨122999116646365502676298829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81999411097577001784199219 122999116646365502676298829)
          ·
            refine ⟨46124668742387063503612061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122999116646365502676298829 46124668742387063503612061)
            ·
              refine ⟨17296750778395148813854523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46124668742387063503612061 17296750778395148813854523)
              ·
                refine ⟨25945126167592723220781785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17296750778395148813854523 25945126167592723220781785)
                ·
                  refine ⟨19458844625694542415586339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25945126167592723220781785 19458844625694542415586339)
                  ·
                    refine ⟨29188266938541813623379509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19458844625694542415586339 29188266938541813623379509)
                    ·
                      refine ⟨2736400025488295027191829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29188266938541813623379509 2736400025488295027191829)
                      ·
                        rfl

theorem cell23_5329120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_5329120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329120 prefixEnd_5329120 := by exact prefixLift 5329120
  have htrace : WordTrace (prefixWord ++ tailWord_5329120) baseStart_5329120 baseEnd_5329120 := by
    simpa [prefixWord, tailWord_5329120, baseEnd_5329120] using wordTrace_append hprefix tailTrace_5329120
  have hstable : (prefixWord ++ tailWord_5329120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329120).length < 2 ^ (prefixWord ++ tailWord_5329120).sum := by decide
  have hdescent : baseEnd_5329120 < baseStart_5329120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329227 : List Nat := [1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 3]
def baseStart_5329227 : Nat := 118140960795 + 5329227 * 2 ^ 59
def prefixEnd_5329227 : Nat := 4983230072969 + 3 ^ 40 * 5329227 * 2
def baseEnd_5329227 : Nat := 2736454967918326108553837

theorem tailTrace_5329227 : CollatzResearch.WordTrace tailWord_5329227 prefixEnd_5329227 2736454967918326108553837 := by
  unfold tailWord_5329227
  simp only [CollatzResearch.WordTrace]
  refine ⟨194372877064128213355209935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129581918042752142236806623 194372877064128213355209935)
  ·
    refine ⟨291559315596192320032814903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194372877064128213355209935 291559315596192320032814903)
    ·
      refine ⟨437338973394288480049222355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291559315596192320032814903 437338973394288480049222355)
      ·
        refine ⟨656008460091432720073833533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437338973394288480049222355 656008460091432720073833533)
        ·
          refine ⟨246003172534287270027687575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 656008460091432720073833533 246003172534287270027687575)
          ·
            refine ⟨369004758801430905041531363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246003172534287270027687575 369004758801430905041531363)
            ·
              refine ⟨553507138202146357562297045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369004758801430905041531363 553507138202146357562297045)
              ·
                refine ⟨12972823551612805255366337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 553507138202146357562297045 12972823551612805255366337)
                ·
                  refine ⟨9729617663709603941524753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12972823551612805255366337 9729617663709603941524753)
                  ·
                    refine ⟨7297213247782202956143565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9729617663709603941524753 7297213247782202956143565)
                    ·
                      refine ⟨2736454967918326108553837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7297213247782202956143565 2736454967918326108553837)
                      ·
                        rfl

theorem cell23_5329227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 3].length) (baseStart_5329227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329227 prefixEnd_5329227 := by exact prefixLift 5329227
  have htrace : WordTrace (prefixWord ++ tailWord_5329227) baseStart_5329227 baseEnd_5329227 := by
    simpa [prefixWord, tailWord_5329227, baseEnd_5329227] using wordTrace_append hprefix tailTrace_5329227
  have hstable : (prefixWord ++ tailWord_5329227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329227).length < 2 ^ (prefixWord ++ tailWord_5329227).sum := by decide
  have hdescent : baseEnd_5329227 < baseStart_5329227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329247 : List Nat := [1, 1, 2, 3, 1, 2, 5, 2, 6]
def baseStart_5329247 : Nat := 118140960795 + 5329247 * 2 ^ 59
def prefixEnd_5329247 : Nat := 4983230072969 + 3 ^ 40 * 5329247 * 2
def baseEnd_5329247 : Nat := 304051693059046225589305

theorem tailTrace_5329247 : CollatzResearch.WordTrace tailWord_5329247 prefixEnd_5329247 304051693059046225589305 := by
  unfold tailWord_5329247
  simp only [CollatzResearch.WordTrace]
  refine ⟨194373606524055756770937995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129582404349370504513958663 194373606524055756770937995)
  ·
    refine ⟨291560409786083635156406993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194373606524055756770937995 291560409786083635156406993)
    ·
      refine ⟨218670307339562726367305245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291560409786083635156406993 218670307339562726367305245)
      ·
        refine ⟨82001365252336022387739467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218670307339562726367305245 82001365252336022387739467)
        ·
          refine ⟨123002047878504033581609201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82001365252336022387739467 123002047878504033581609201)
          ·
            refine ⟨92251535908878025186206901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123002047878504033581609201 92251535908878025186206901)
            ·
              refine ⟨8648581491457314861206897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92251535908878025186206901 8648581491457314861206897)
              ·
                refine ⟨6486436118592986145905173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8648581491457314861206897 6486436118592986145905173)
                ·
                  refine ⟨304051693059046225589305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6486436118592986145905173 304051693059046225589305)
                  ·
                    rfl

theorem cell23_5329247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 6].length) (baseStart_5329247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329247 prefixEnd_5329247 := by exact prefixLift 5329247
  have htrace : WordTrace (prefixWord ++ tailWord_5329247) baseStart_5329247 baseEnd_5329247 := by
    simpa [prefixWord, tailWord_5329247, baseEnd_5329247] using wordTrace_append hprefix tailTrace_5329247
  have hstable : (prefixWord ++ tailWord_5329247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329247).length < 2 ^ (prefixWord ++ tailWord_5329247).sum := by decide
  have hdescent : baseEnd_5329247 < baseStart_5329247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329264 : List Nat := [2, 1, 1, 1, 4, 4, 3, 1, 6]
def baseStart_5329264 : Nat := 118140960795 + 5329264 * 2 ^ 59
def prefixEnd_5329264 : Nat := 4983230072969 + 3 ^ 40 * 5329264 * 2
def baseEnd_5329264 : Nat := 304052662966949162643463

theorem tailTrace_5329264 : CollatzResearch.WordTrace tailWord_5329264 prefixEnd_5329264 304052662966949162643463 := by
  unfold tailWord_5329264
  simp only [CollatzResearch.WordTrace]
  refine ⟨97187113282497084337153423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129582817709996112449537897 97187113282497084337153423)
  ·
    refine ⟨145780669923745626505730135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97187113282497084337153423 145780669923745626505730135)
    ·
      refine ⟨218671004885618439758595203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145780669923745626505730135 218671004885618439758595203)
      ·
        refine ⟨328006507328427659637892805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218671004885618439758595203 328006507328427659637892805)
        ·
          refine ⟨61501220124080186182104901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 328006507328427659637892805 61501220124080186182104901)
          ·
            refine ⟨11531478773265034909144669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61501220124080186182104901 11531478773265034909144669)
            ·
              refine ⟨4324304539974388090929251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11531478773265034909144669 4324304539974388090929251)
              ·
                refine ⟨6486456809961582136393877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4324304539974388090929251 6486456809961582136393877)
                ·
                  refine ⟨304052662966949162643463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6486456809961582136393877 304052662966949162643463)
                  ·
                    rfl

theorem cell23_5329264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 6].length) (baseStart_5329264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329264 prefixEnd_5329264 := by exact prefixLift 5329264
  have htrace : WordTrace (prefixWord ++ tailWord_5329264) baseStart_5329264 baseEnd_5329264 := by
    simpa [prefixWord, tailWord_5329264, baseEnd_5329264] using wordTrace_append hprefix tailTrace_5329264
  have hstable : (prefixWord ++ tailWord_5329264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329264).length < 2 ^ (prefixWord ++ tailWord_5329264).sum := by decide
  have hdescent : baseEnd_5329264 < baseStart_5329264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329284 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 1, 5, 2]
def baseStart_5329284 : Nat := 118140960795 + 5329284 * 2 ^ 59
def prefixEnd_5329284 : Nat := 4983230072969 + 3 ^ 40 * 5329284 * 2
def baseEnd_5329284 : Nat := 2736484236315632385541075

theorem tailTrace_5329284 : CollatzResearch.WordTrace tailWord_5329284 prefixEnd_5329284 2736484236315632385541075 := by
  unfold tailWord_5329284
  simp only [CollatzResearch.WordTrace]
  refine ⟨97187478012460856045017453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129583304016614474726689937 97187478012460856045017453)
  ·
    refine ⟨36445304254672821016881545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97187478012460856045017453 36445304254672821016881545)
    ·
      refine ⟨27333978191004615762661159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36445304254672821016881545 27333978191004615762661159)
      ·
        refine ⟨41000967286506923643991739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27333978191004615762661159 41000967286506923643991739)
        ·
          refine ⟨61501450929760385465987609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41000967286506923643991739 61501450929760385465987609)
          ·
            refine ⟨46126088197320289099490707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61501450929760385465987609 46126088197320289099490707)
            ·
              refine ⟨69189132295980433649236061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46126088197320289099490707 69189132295980433649236061)
              ·
                refine ⟨25945924610992662618463523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69189132295980433649236061 25945924610992662618463523)
                ·
                  refine ⟨38918886916488993927695285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25945924610992662618463523 38918886916488993927695285)
                  ·
                    refine ⟨3648645648420843180721433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38918886916488993927695285 3648645648420843180721433)
                    ·
                      refine ⟨2736484236315632385541075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3648645648420843180721433 2736484236315632385541075)
                      ·
                        rfl

theorem cell23_5329284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_5329284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329284 prefixEnd_5329284 := by exact prefixLift 5329284
  have htrace : WordTrace (prefixWord ++ tailWord_5329284) baseStart_5329284 baseEnd_5329284 := by
    simpa [prefixWord, tailWord_5329284, baseEnd_5329284] using wordTrace_append hprefix tailTrace_5329284
  have hstable : (prefixWord ++ tailWord_5329284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329284).length < 2 ^ (prefixWord ++ tailWord_5329284).sum := by decide
  have hdescent : baseEnd_5329284 < baseStart_5329284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329302 : List Nat := [5, 3, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_5329302 : Nat := 118140960795 + 5329302 * 2 ^ 59
def prefixEnd_5329302 : Nat := 4983230072969 + 3 ^ 40 * 5329302 * 2
def baseEnd_5329302 : Nat := 912164492989137771705331

theorem tailTrace_5329302 : CollatzResearch.WordTrace tailWord_5329302 prefixEnd_5329302 912164492989137771705331 := by
  unfold tailWord_5329302
  simp only [CollatzResearch.WordTrace]
  refine ⟨12148475783678531322761885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129583741692571000776126773 12148475783678531322761885)
  ·
    refine ⟨4555678418879449246035707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12148475783678531322761885 4555678418879449246035707)
    ·
      refine ⟨6833517628319173869053561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4555678418879449246035707 6833517628319173869053561)
      ·
        refine ⟨5125138221239380401790171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6833517628319173869053561 5125138221239380401790171)
        ·
          refine ⟨7687707331859070602685257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5125138221239380401790171 7687707331859070602685257)
          ·
            refine ⟨5765780498894302952013943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7687707331859070602685257 5765780498894302952013943)
            ·
              refine ⟨8648670748341454428020915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5765780498894302952013943 8648670748341454428020915)
              ·
                refine ⟨12973006122512181642031373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8648670748341454428020915 12973006122512181642031373)
                ·
                  refine ⟨4864877295942068115761765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12973006122512181642031373 4864877295942068115761765)
                  ·
                    refine ⟨912164492989137771705331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4864877295942068115761765 912164492989137771705331)
                    ·
                      rfl

theorem cell23_5329302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_5329302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329302 prefixEnd_5329302 := by exact prefixLift 5329302
  have htrace : WordTrace (prefixWord ++ tailWord_5329302) baseStart_5329302 baseEnd_5329302 := by
    simpa [prefixWord, tailWord_5329302, baseEnd_5329302] using wordTrace_append hprefix tailTrace_5329302
  have hstable : (prefixWord ++ tailWord_5329302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329302).length < 2 ^ (prefixWord ++ tailWord_5329302).sum := by decide
  have hdescent : baseEnd_5329302 < baseStart_5329302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329314 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_5329314 : Nat := 118140960795 + 5329314 * 2 ^ 59
def prefixEnd_5329314 : Nat := 4983230072969 + 3 ^ 40 * 5329314 * 2
def baseEnd_5329314 : Nat := 2736499640735267268165937

theorem tailTrace_5329314 : CollatzResearch.WordTrace tailWord_5329314 prefixEnd_5329314 2736499640735267268165937 := by
  unfold tailWord_5329314
  simp only [CollatzResearch.WordTrace]
  refine ⟨48594012553703256803406749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129584033476542018142417997 48594012553703256803406749)
  ·
    refine ⟨18222754707638721301277531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48594012553703256803406749 18222754707638721301277531)
    ·
      refine ⟨27334132061458081951916297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18222754707638721301277531 27334132061458081951916297)
      ·
        refine ⟨20500599046093561463937223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27334132061458081951916297 20500599046093561463937223)
        ·
          refine ⟨30750898569140342195905835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20500599046093561463937223 30750898569140342195905835)
          ·
            refine ⟨46126347853710513293858753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30750898569140342195905835 46126347853710513293858753)
            ·
              refine ⟨34594760890282884970394065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46126347853710513293858753 34594760890282884970394065)
              ·
                refine ⟨25946070667712163727795549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34594760890282884970394065 25946070667712163727795549)
                ·
                  refine ⟨9729776500392061397923331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25946070667712163727795549 9729776500392061397923331)
                  ·
                    refine ⟨14594664750588092096884997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9729776500392061397923331 14594664750588092096884997)
                    ·
                      refine ⟨2736499640735267268165937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14594664750588092096884997 2736499640735267268165937)
                      ·
                        rfl

theorem cell23_5329314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_5329314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329314 prefixEnd_5329314 := by exact prefixLift 5329314
  have htrace : WordTrace (prefixWord ++ tailWord_5329314) baseStart_5329314 baseEnd_5329314 := by
    simpa [prefixWord, tailWord_5329314, baseEnd_5329314] using wordTrace_append hprefix tailTrace_5329314
  have hstable : (prefixWord ++ tailWord_5329314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329314).length < 2 ^ (prefixWord ++ tailWord_5329314).sum := by decide
  have hdescent : baseEnd_5329314 < baseStart_5329314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329317 : List Nat := [1, 3, 1, 2, 1, 1, 3, 4, 1, 1, 5]
def baseStart_5329317 : Nat := 118140960795 + 5329317 * 2 ^ 59
def prefixEnd_5329317 : Nat := 4983230072969 + 3 ^ 40 * 5329317 * 2
def baseEnd_5329317 : Nat := 2736501181177230756428423

theorem tailTrace_5329317 : CollatzResearch.WordTrace tailWord_5329317 prefixEnd_5329317 2736501181177230756428423 := by
  unfold tailWord_5329317
  simp only [CollatzResearch.WordTrace]
  refine ⟨194376159633802158725986205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129584106422534772483990803 194376159633802158725986205)
  ·
    refine ⟨72891059862675809522244827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194376159633802158725986205 72891059862675809522244827)
    ·
      refine ⟨109336589794013714283367241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72891059862675809522244827 109336589794013714283367241)
      ·
        refine ⟨82002442345510285712525431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109336589794013714283367241 82002442345510285712525431)
        ·
          refine ⟨123003663518265428568788147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82002442345510285712525431 123003663518265428568788147)
          ·
            refine ⟨184505495277398142853182221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123003663518265428568788147 184505495277398142853182221)
            ·
              refine ⟨69189560729024303569943333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184505495277398142853182221 69189560729024303569943333)
              ·
                refine ⟨12973042636692056919364375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69189560729024303569943333 12973042636692056919364375)
                ·
                  refine ⟨19459563955038085379046563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12973042636692056919364375 19459563955038085379046563)
                  ·
                    refine ⟨29189345932557128068569845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19459563955038085379046563 29189345932557128068569845)
                    ·
                      refine ⟨2736501181177230756428423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29189345932557128068569845 2736501181177230756428423)
                      ·
                        rfl

theorem cell23_5329317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_5329317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329317 prefixEnd_5329317 := by exact prefixLift 5329317
  have htrace : WordTrace (prefixWord ++ tailWord_5329317) baseStart_5329317 baseEnd_5329317 := by
    simpa [prefixWord, tailWord_5329317, baseEnd_5329317] using wordTrace_append hprefix tailTrace_5329317
  have hstable : (prefixWord ++ tailWord_5329317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329317).length < 2 ^ (prefixWord ++ tailWord_5329317).sum := by decide
  have hdescent : baseEnd_5329317 < baseStart_5329317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329337 : List Nat := [1, 2, 1, 4, 3, 1, 2, 9]
def baseStart_5329337 : Nat := 118140960795 + 5329337 * 2 ^ 59
def prefixEnd_5329337 : Nat := 4983230072969 + 3 ^ 40 * 5329337 * 2
def baseEnd_5329337 : Nat := 101352275955197062154753

theorem tailTrace_5329337 : CollatzResearch.WordTrace tailWord_5329337 prefixEnd_5329337 101352275955197062154753 := by
  unfold tailWord_5329337
  simp only [CollatzResearch.WordTrace]
  refine ⟨194376889093729702141714265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129584592729153134761142843 194376889093729702141714265)
  ·
    refine ⟨145782666820297276606285699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194376889093729702141714265 145782666820297276606285699)
    ·
      refine ⟨218674000230445914909428549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145782666820297276606285699 218674000230445914909428549)
      ·
        refine ⟨41001375043208609045517853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218674000230445914909428549 41001375043208609045517853)
        ·
          refine ⟨15375515641203228392069195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41001375043208609045517853 15375515641203228392069195)
          ·
            refine ⟨23063273461804842588103793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15375515641203228392069195 23063273461804842588103793)
            ·
              refine ⟨17297455096353631941077845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23063273461804842588103793 17297455096353631941077845)
              ·
                refine ⟨101352275955197062154753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17297455096353631941077845 101352275955197062154753)
                ·
                  rfl

theorem cell23_5329337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 9].length) (baseStart_5329337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329337 prefixEnd_5329337 := by exact prefixLift 5329337
  have htrace : WordTrace (prefixWord ++ tailWord_5329337) baseStart_5329337 baseEnd_5329337 := by
    simpa [prefixWord, tailWord_5329337, baseEnd_5329337] using wordTrace_append hprefix tailTrace_5329337
  have hstable : (prefixWord ++ tailWord_5329337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329337).length < 2 ^ (prefixWord ++ tailWord_5329337).sum := by decide
  have hdescent : baseEnd_5329337 < baseStart_5329337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329365 : List Nat := [1, 3, 2, 3, 1, 3, 1, 4, 1, 2, 2]
def baseStart_5329365 : Nat := 118140960795 + 5329365 * 2 ^ 59
def prefixEnd_5329365 : Nat := 4983230072969 + 3 ^ 40 * 5329365 * 2
def baseEnd_5329365 : Nat := 2736525828248646568628203

theorem tailTrace_5329365 : CollatzResearch.WordTrace tailWord_5329365 prefixEnd_5329365 2736525828248646568628203 := by
  unfold tailWord_5329365
  simp only [CollatzResearch.WordTrace]
  refine ⟨194377910337628262923733549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129585273558418841949155699 194377910337628262923733549)
  ·
    refine ⟨72891716376610598596400081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194377910337628262923733549 72891716376610598596400081)
    ·
      refine ⟨54668787282457948947300061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72891716376610598596400081 54668787282457948947300061)
      ·
        refine ⟨20500795230921730855237523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54668787282457948947300061 20500795230921730855237523)
        ·
          refine ⟨30751192846382596282856285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20500795230921730855237523 30751192846382596282856285)
          ·
            refine ⟨11531697317393473606071107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30751192846382596282856285 11531697317393473606071107)
            ·
              refine ⟨17297545976090210409106661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11531697317393473606071107 17297545976090210409106661)
              ·
                refine ⟨3243289870516914451707499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17297545976090210409106661 3243289870516914451707499)
                ·
                  refine ⟨4864934805775371677561249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3243289870516914451707499 4864934805775371677561249)
                  ·
                    refine ⟨3648701104331528758170937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4864934805775371677561249 3648701104331528758170937)
                    ·
                      refine ⟨2736525828248646568628203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3648701104331528758170937 2736525828248646568628203)
                      ·
                        rfl

theorem cell23_5329365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_5329365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329365 prefixEnd_5329365 := by exact prefixLift 5329365
  have htrace : WordTrace (prefixWord ++ tailWord_5329365) baseStart_5329365 baseEnd_5329365 := by
    simpa [prefixWord, tailWord_5329365, baseEnd_5329365] using wordTrace_append hprefix tailTrace_5329365
  have hstable : (prefixWord ++ tailWord_5329365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329365).length < 2 ^ (prefixWord ++ tailWord_5329365).sum := by decide
  have hdescent : baseEnd_5329365 < baseStart_5329365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329387 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 4]
def baseStart_5329387 : Nat := 118140960795 + 5329387 * 2 ^ 59
def prefixEnd_5329387 : Nat := 4983230072969 + 3 ^ 40 * 5329387 * 2
def baseEnd_5329387 : Nat := 2736537124823045482553101

theorem tailTrace_5329387 : CollatzResearch.WordTrace tailWord_5329387 prefixEnd_5329387 2736537124823045482553101 := by
  unfold tailWord_5329387
  simp only [CollatzResearch.WordTrace]
  refine ⟨194378712743548560681034415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129585808495699040454022943 194378712743548560681034415)
  ·
    refine ⟨291568069115322841021551623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194378712743548560681034415 291568069115322841021551623)
    ·
      refine ⟨437352103672984261532327435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291568069115322841021551623 437352103672984261532327435)
      ·
        refine ⟨656028155509476392298491153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437352103672984261532327435 656028155509476392298491153)
        ·
          refine ⟨492021116632107294223868365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 656028155509476392298491153 492021116632107294223868365)
          ·
            refine ⟨184507918737040235333950637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 492021116632107294223868365 184507918737040235333950637)
            ·
              refine ⟨69190469526390088250231489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184507918737040235333950637 69190469526390088250231489)
              ·
                refine ⟨51892852144792566187673617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69190469526390088250231489 51892852144792566187673617)
                ·
                  refine ⟨38919639108594424640755213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51892852144792566187673617 38919639108594424640755213)
                  ·
                    refine ⟨14594864665722909240283205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38919639108594424640755213 14594864665722909240283205)
                    ·
                      refine ⟨2736537124823045482553101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14594864665722909240283205 2736537124823045482553101)
                      ·
                        rfl

theorem cell23_5329387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 4].length) (baseStart_5329387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329387 prefixEnd_5329387 := by exact prefixLift 5329387
  have htrace : WordTrace (prefixWord ++ tailWord_5329387) baseStart_5329387 baseEnd_5329387 := by
    simpa [prefixWord, tailWord_5329387, baseEnd_5329387] using wordTrace_append hprefix tailTrace_5329387
  have hstable : (prefixWord ++ tailWord_5329387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329387).length < 2 ^ (prefixWord ++ tailWord_5329387).sum := by decide
  have hdescent : baseEnd_5329387 < baseStart_5329387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329391 : List Nat := [1, 1, 2, 1, 4, 1, 1, 6, 1, 3, 2]
def baseStart_5329391 : Nat := 118140960795 + 5329391 * 2 ^ 59
def prefixEnd_5329391 : Nat := 4983230072969 + 3 ^ 40 * 5329391 * 2
def baseEnd_5329391 : Nat := 2736539178745663466903083

theorem tailTrace_5329391 : CollatzResearch.WordTrace tailWord_5329391 prefixEnd_5329391 2736539178745663466903083 := by
  unfold tailWord_5329391
  simp only [CollatzResearch.WordTrace]
  refine ⟨194378858635534069364180027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129585905757022712909453351 194378858635534069364180027)
  ·
    refine ⟨291568287953301104046270041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194378858635534069364180027 291568287953301104046270041)
    ·
      refine ⟨218676215964975828034702531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291568287953301104046270041 218676215964975828034702531)
      ·
        refine ⟨328014323947463742052053797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218676215964975828034702531 328014323947463742052053797)
        ·
          refine ⟨61502685740149451634760087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 328014323947463742052053797 61502685740149451634760087)
          ·
            refine ⟨92254028610224177452140131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61502685740149451634760087 92254028610224177452140131)
            ·
              refine ⟨138381042915336266178210197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92254028610224177452140131 138381042915336266178210197)
              ·
                refine ⟨6486611386656387477103603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 138381042915336266178210197 6486611386656387477103603)
                ·
                  refine ⟨9729917079984581215655405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6486611386656387477103603 9729917079984581215655405)
                  ·
                    refine ⟨3648718904994217955870777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9729917079984581215655405 3648718904994217955870777)
                    ·
                      refine ⟨2736539178745663466903083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3648718904994217955870777 2736539178745663466903083)
                      ·
                        rfl

theorem cell23_5329391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 3, 2].length) (baseStart_5329391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329391 prefixEnd_5329391 := by exact prefixLift 5329391
  have htrace : WordTrace (prefixWord ++ tailWord_5329391) baseStart_5329391 baseEnd_5329391 := by
    simpa [prefixWord, tailWord_5329391, baseEnd_5329391] using wordTrace_append hprefix tailTrace_5329391
  have hstable : (prefixWord ++ tailWord_5329391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329391).length < 2 ^ (prefixWord ++ tailWord_5329391).sum := by decide
  have hdescent : baseEnd_5329391 < baseStart_5329391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329407 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 5]
def baseStart_5329407 : Nat := 118140960795 + 5329407 * 2 ^ 59
def prefixEnd_5329407 : Nat := 4983230072969 + 3 ^ 40 * 5329407 * 2
def baseEnd_5329407 : Nat := 2736547394436135404303009

theorem tailTrace_5329407 : CollatzResearch.WordTrace tailWord_5329407 prefixEnd_5329407 2736547394436135404303009 := by
  unfold tailWord_5329407
  simp only [CollatzResearch.WordTrace]
  refine ⟨194379442203476104096762475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129586294802317402731174983 194379442203476104096762475)
  ·
    refine ⟨291569163305214156145143713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194379442203476104096762475 291569163305214156145143713)
    ·
      refine ⟨218676872478910617108857785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291569163305214156145143713 218676872478910617108857785)
      ·
        refine ⟨164007654359182962831643339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218676872478910617108857785 164007654359182962831643339)
        ·
          refine ⟨246011481538774444247465009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164007654359182962831643339 246011481538774444247465009)
          ·
            refine ⟨184508611154080833185598757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246011481538774444247465009 184508611154080833185598757)
            ·
              refine ⟨34595364591390156222299767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184508611154080833185598757 34595364591390156222299767)
              ·
                refine ⟨51893046887085234333449651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34595364591390156222299767 51893046887085234333449651)
                ·
                  refine ⟨77839570330627851500174477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51893046887085234333449651 77839570330627851500174477)
                  ·
                    refine ⟨29189838873985444312565429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77839570330627851500174477 29189838873985444312565429)
                    ·
                      refine ⟨2736547394436135404303009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29189838873985444312565429 2736547394436135404303009)
                      ·
                        rfl

theorem cell23_5329407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_5329407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329407 prefixEnd_5329407 := by exact prefixLift 5329407
  have htrace : WordTrace (prefixWord ++ tailWord_5329407) baseStart_5329407 baseEnd_5329407 := by
    simpa [prefixWord, tailWord_5329407, baseEnd_5329407] using wordTrace_append hprefix tailTrace_5329407
  have hstable : (prefixWord ++ tailWord_5329407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329407).length < 2 ^ (prefixWord ++ tailWord_5329407).sum := by decide
  have hdescent : baseEnd_5329407 < baseStart_5329407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329415 : List Nat := [1, 1, 4, 3, 3, 2, 1, 2, 2, 1, 3]
def baseStart_5329415 : Nat := 118140960795 + 5329415 * 2 ^ 59
def prefixEnd_5329415 : Nat := 4983230072969 + 3 ^ 40 * 5329415 * 2
def baseEnd_5329415 : Nat := 2736551502281371373002973

theorem tailTrace_5329415 : CollatzResearch.WordTrace tailWord_5329415 prefixEnd_5329415 2736551502281371373002973 := by
  unfold tailWord_5329415
  simp only [CollatzResearch.WordTrace]
  refine ⟨194379733987447121463053699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129586489324964747642035799 194379733987447121463053699)
  ·
    refine ⟨291569600981170682194580549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194379733987447121463053699 291569600981170682194580549)
    ·
      refine ⟨54669300183969502911483853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 291569600981170682194580549 54669300183969502911483853)
      ·
        refine ⟨20500987568988563591806445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54669300183969502911483853 20500987568988563591806445)
        ·
          refine ⟨7687870338370711346927417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20500987568988563591806445 7687870338370711346927417)
          ·
            refine ⟨5765902753778033510195563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7687870338370711346927417 5765902753778033510195563)
            ·
              refine ⟨8648854130667050265293345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5765902753778033510195563 8648854130667050265293345)
              ·
                refine ⟨6486640598000287698970009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8648854130667050265293345 6486640598000287698970009)
                ·
                  refine ⟨4864980448500215774227507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6486640598000287698970009 4864980448500215774227507)
                  ·
                    refine ⟨7297470672750323661341261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4864980448500215774227507 7297470672750323661341261)
                    ·
                      refine ⟨2736551502281371373002973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7297470672750323661341261 2736551502281371373002973)
                      ·
                        rfl

theorem cell23_5329415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_5329415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329415 prefixEnd_5329415 := by exact prefixLift 5329415
  have htrace : WordTrace (prefixWord ++ tailWord_5329415) baseStart_5329415 baseEnd_5329415 := by
    simpa [prefixWord, tailWord_5329415, baseEnd_5329415] using wordTrace_append hprefix tailTrace_5329415
  have hstable : (prefixWord ++ tailWord_5329415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329415).length < 2 ^ (prefixWord ++ tailWord_5329415).sum := by decide
  have hdescent : baseEnd_5329415 < baseStart_5329415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329434 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4]
def baseStart_5329434 : Nat := 118140960795 + 5329434 * 2 ^ 59
def prefixEnd_5329434 : Nat := 4983230072969 + 3 ^ 40 * 5329434 * 2
def baseEnd_5329434 : Nat := 2736561258413806798665385

theorem tailTrace_5329434 : CollatzResearch.WordTrace tailWord_5329434 prefixEnd_5329434 2736561258413806798665385 := by
  unfold tailWord_5329434
  simp only [CollatzResearch.WordTrace]
  refine ⟨48595106743594571926998839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129586951316252191805330237 48595106743594571926998839)
  ·
    refine ⟨72892660115391857890498259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48595106743594571926998839 72892660115391857890498259)
    ·
      refine ⟨109338990173087786835747389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72892660115391857890498259 109338990173087786835747389)
      ·
        refine ⟨41002121314907920063405271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109338990173087786835747389 41002121314907920063405271)
        ·
          refine ⟨61503181972361880095107907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41002121314907920063405271 61503181972361880095107907)
          ·
            refine ⟨92254772958542820142661861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61503181972361880095107907 92254772958542820142661861)
            ·
              refine ⟨17297769929726778776749099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92254772958542820142661861 17297769929726778776749099)
              ·
                refine ⟨25946654894590168165123649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17297769929726778776749099 25946654894590168165123649)
                ·
                  refine ⟨19459991170942626123842737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25946654894590168165123649 19459991170942626123842737)
                  ·
                    refine ⟨14594993378206969592882053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19459991170942626123842737 14594993378206969592882053)
                    ·
                      refine ⟨2736561258413806798665385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14594993378206969592882053 2736561258413806798665385)
                      ·
                        rfl

theorem cell23_5329434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_5329434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329434 prefixEnd_5329434 := by exact prefixLift 5329434
  have htrace : WordTrace (prefixWord ++ tailWord_5329434) baseStart_5329434 baseEnd_5329434 := by
    simpa [prefixWord, tailWord_5329434, baseEnd_5329434] using wordTrace_append hprefix tailTrace_5329434
  have hstable : (prefixWord ++ tailWord_5329434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329434).length < 2 ^ (prefixWord ++ tailWord_5329434).sum := by decide
  have hdescent : baseEnd_5329434 < baseStart_5329434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329467 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 5]
def baseStart_5329467 : Nat := 118140960795 + 5329467 * 2 ^ 59
def prefixEnd_5329467 : Nat := 4983230072969 + 3 ^ 40 * 5329467 * 2
def baseEnd_5329467 : Nat := 2736578203275405169552733

theorem tailTrace_5329467 : CollatzResearch.WordTrace tailWord_5329467 prefixEnd_5329467 2736578203275405169552733 := by
  unfold tailWord_5329467
  simp only [CollatzResearch.WordTrace]
  refine ⟨194381630583258734343946655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129587753722172489562631103 194381630583258734343946655)
  ·
    refine ⟨291572445874888101515919983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194381630583258734343946655 291572445874888101515919983)
    ·
      refine ⟨437358668812332152273879975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291572445874888101515919983 437358668812332152273879975)
      ·
        refine ⟨656038003218498228410819963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437358668812332152273879975 656038003218498228410819963)
        ·
          refine ⟨984057004827747342616229945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656038003218498228410819963 984057004827747342616229945)
          ·
            refine ⟨738042753620810506962172459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 984057004827747342616229945 738042753620810506962172459)
            ·
              refine ⟨1107064130431215760443258689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738042753620810506962172459 1107064130431215760443258689)
              ·
                refine ⟨830298097823411820332444017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1107064130431215760443258689 830298097823411820332444017)
                ·
                  refine ⟨622723573367558865249333013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 830298097823411820332444017 622723573367558865249333013)
                  ·
                    refine ⟨29190167501604321808562485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 622723573367558865249333013 29190167501604321808562485)
                    ·
                      refine ⟨2736578203275405169552733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29190167501604321808562485 2736578203275405169552733)
                      ·
                        rfl

theorem cell23_5329467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 5].length) (baseStart_5329467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329467 prefixEnd_5329467 := by exact prefixLift 5329467
  have htrace : WordTrace (prefixWord ++ tailWord_5329467) baseStart_5329467 baseEnd_5329467 := by
    simpa [prefixWord, tailWord_5329467, baseEnd_5329467] using wordTrace_append hprefix tailTrace_5329467
  have hstable : (prefixWord ++ tailWord_5329467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329467).length < 2 ^ (prefixWord ++ tailWord_5329467).sum := by decide
  have hdescent : baseEnd_5329467 < baseStart_5329467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329478 : List Nat := [6, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_5329478 : Nat := 118140960795 + 5329478 * 2 ^ 59
def prefixEnd_5329478 : Nat := 4983230072969 + 3 ^ 40 * 5329478 * 2
def baseEnd_5329478 : Nat := 304064872395844958501687

theorem tailTrace_5329478 : CollatzResearch.WordTrace tailWord_5329478 prefixEnd_5329478 304064872395844958501687 := by
  unfold tailWord_5329478
  simp only [CollatzResearch.WordTrace]
  refine ⟨6074438493319340100706159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 129588021190812588815064725 6074438493319340100706159)
  ·
    refine ⟨9111657739979010151059239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6074438493319340100706159 9111657739979010151059239)
    ·
      refine ⟨13667486609968515226588859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9111657739979010151059239 13667486609968515226588859)
      ·
        refine ⟨20501229914952772839883289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13667486609968515226588859 20501229914952772839883289)
        ·
          refine ⟨15375922436214579629912467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20501229914952772839883289 15375922436214579629912467)
          ·
            refine ⟨23063883654321869444868701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15375922436214579629912467 23063883654321869444868701)
            ·
              refine ⟨8648956370370701041825763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23063883654321869444868701 8648956370370701041825763)
              ·
                refine ⟨12973434555556051562738645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8648956370370701041825763 12973434555556051562738645)
                ·
                  refine ⟨304064872395844958501687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12973434555556051562738645 304064872395844958501687)
                  ·
                    rfl

theorem cell23_5329478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_5329478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329478 prefixEnd_5329478 := by exact prefixLift 5329478
  have htrace : WordTrace (prefixWord ++ tailWord_5329478) baseStart_5329478 baseEnd_5329478 := by
    simpa [prefixWord, tailWord_5329478, baseEnd_5329478] using wordTrace_append hprefix tailTrace_5329478
  have hstable : (prefixWord ++ tailWord_5329478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329478).length < 2 ^ (prefixWord ++ tailWord_5329478).sum := by decide
  have hdescent : baseEnd_5329478 < baseStart_5329478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329484 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 1, 2, 5]
def baseStart_5329484 : Nat := 118140960795 + 5329484 * 2 ^ 59
def prefixEnd_5329484 : Nat := 4983230072969 + 3 ^ 40 * 5329484 * 2
def baseEnd_5329484 : Nat := 2736586932446531603040155

theorem tailTrace_5329484 : CollatzResearch.WordTrace tailWord_5329484 prefixEnd_5329484 2736586932446531603040155 := by
  unfold tailWord_5329484
  simp only [CollatzResearch.WordTrace]
  refine ⟨97191125312098573123657753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129588167082798097498210337 97191125312098573123657753)
  ·
    refine ⟨72893343984073929842743315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97191125312098573123657753 72893343984073929842743315)
    ·
      refine ⟨109340015976110894764114973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72893343984073929842743315 109340015976110894764114973)
      ·
        refine ⟨41002505991041585536543115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109340015976110894764114973 41002505991041585536543115)
        ·
          refine ⟨61503758986562378304814673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41002505991041585536543115 61503758986562378304814673)
          ·
            refine ⟨46127819239921783728611005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61503758986562378304814673 46127819239921783728611005)
            ·
              refine ⟨17297932214970668898229127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46127819239921783728611005 17297932214970668898229127)
              ·
                refine ⟨25946898322456003347343691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17297932214970668898229127 25946898322456003347343691)
                ·
                  refine ⟨38920347483684005021015537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25946898322456003347343691 38920347483684005021015537)
                  ·
                    refine ⟨29190260612763003765761653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38920347483684005021015537 29190260612763003765761653)
                    ·
                      refine ⟨2736586932446531603040155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29190260612763003765761653 2736586932446531603040155)
                      ·
                        rfl

theorem cell23_5329484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_5329484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329484 prefixEnd_5329484 := by exact prefixLift 5329484
  have htrace : WordTrace (prefixWord ++ tailWord_5329484) baseStart_5329484 baseEnd_5329484 := by
    simpa [prefixWord, tailWord_5329484, baseEnd_5329484] using wordTrace_append hprefix tailTrace_5329484
  have hstable : (prefixWord ++ tailWord_5329484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329484).length < 2 ^ (prefixWord ++ tailWord_5329484).sum := by decide
  have hdescent : baseEnd_5329484 < baseStart_5329484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329511 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 4, 4, 2]
def baseStart_5329511 : Nat := 118140960795 + 5329511 * 2 ^ 59
def prefixEnd_5329511 : Nat := 4983230072969 + 3 ^ 40 * 5329511 * 2
def baseEnd_5329511 : Nat := 2736600796424202997402531

theorem tailTrace_5329511 : CollatzResearch.WordTrace tailWord_5329511 prefixEnd_5329511 2736600796424202997402531 := by
  unfold tailWord_5329511
  simp only [CollatzResearch.WordTrace]
  refine ⟨194383235395099329858548387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129588823596732886572365591 194383235395099329858548387)
  ·
    refine ⟨291574853092648994787822581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194383235395099329858548387 291574853092648994787822581)
    ·
      refine ⟨27335142477435843261358367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 291574853092648994787822581 27335142477435843261358367)
      ·
        refine ⟨41002713716153764892037551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27335142477435843261358367 41002713716153764892037551)
        ·
          refine ⟨61504070574230647338056327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41002713716153764892037551 61504070574230647338056327)
          ·
            refine ⟨92256105861345971007084491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61504070574230647338056327 92256105861345971007084491)
            ·
              refine ⟨138384158792018956510626737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92256105861345971007084491 138384158792018956510626737)
              ·
                refine ⟨103788119094014217382970053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138384158792018956510626737 103788119094014217382970053)
                ·
                  refine ⟨19460272330127665759306885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103788119094014217382970053 19460272330127665759306885)
                  ·
                    refine ⟨3648801061898937329870041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19460272330127665759306885 3648801061898937329870041)
                    ·
                      refine ⟨2736600796424202997402531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3648801061898937329870041 2736600796424202997402531)
                      ·
                        rfl

theorem cell23_5329511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_5329511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329511 prefixEnd_5329511 := by exact prefixLift 5329511
  have htrace : WordTrace (prefixWord ++ tailWord_5329511) baseStart_5329511 baseEnd_5329511 := by
    simpa [prefixWord, tailWord_5329511, baseEnd_5329511] using wordTrace_append hprefix tailTrace_5329511
  have hstable : (prefixWord ++ tailWord_5329511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329511).length < 2 ^ (prefixWord ++ tailWord_5329511).sum := by decide
  have hdescent : baseEnd_5329511 < baseStart_5329511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329562 : List Nat := [3, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4]
def baseStart_5329562 : Nat := 118140960795 + 5329562 * 2 ^ 59
def prefixEnd_5329562 : Nat := 4983230072969 + 3 ^ 40 * 5329562 * 2
def baseEnd_5329562 : Nat := 2736626983937582297864797

theorem tailTrace_5329562 : CollatzResearch.WordTrace tailWord_5329562 prefixEnd_5329562 2736626983937582297864797 := by
  unfold tailWord_5329562
  simp only [CollatzResearch.WordTrace]
  refine ⟨48596273879478641392163735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129590063678609710379103293 48596273879478641392163735)
  ·
    refine ⟨72894410819217962088245603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48596273879478641392163735 72894410819217962088245603)
    ·
      refine ⟨109341616228826943132368405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72894410819217962088245603 109341616228826943132368405)
      ·
        refine ⟨5125388260726262959329769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 109341616228826943132368405 5125388260726262959329769)
        ·
          refine ⟨3844041195544697219497327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5125388260726262959329769 3844041195544697219497327)
          ·
            refine ⟨5766061793317045829245991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3844041195544697219497327 5766061793317045829245991)
            ·
              refine ⟨8649092689975568743868987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5766061793317045829245991 8649092689975568743868987)
              ·
                refine ⟨12973639034963353115803481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8649092689975568743868987 12973639034963353115803481)
                ·
                  refine ⟨9730229276222514836852611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12973639034963353115803481 9730229276222514836852611)
                  ·
                    refine ⟨14595343914333772255278917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9730229276222514836852611 14595343914333772255278917)
                    ·
                      refine ⟨2736626983937582297864797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14595343914333772255278917 2736626983937582297864797)
                      ·
                        rfl

theorem cell23_5329562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_5329562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329562 prefixEnd_5329562 := by exact prefixLift 5329562
  have htrace : WordTrace (prefixWord ++ tailWord_5329562) baseStart_5329562 baseEnd_5329562 := by
    simpa [prefixWord, tailWord_5329562, baseEnd_5329562] using wordTrace_append hprefix tailTrace_5329562
  have hstable : (prefixWord ++ tailWord_5329562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329562).length < 2 ^ (prefixWord ++ tailWord_5329562).sum := by decide
  have hdescent : baseEnd_5329562 < baseStart_5329562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329585 : List Nat := [1, 2, 2, 6, 1, 2, 1, 2, 6]
def baseStart_5329585 : Nat := 118140960795 + 5329585 * 2 ^ 59
def prefixEnd_5329585 : Nat := 4983230072969 + 3 ^ 40 * 5329585 * 2
def baseEnd_5329585 : Nat := 304070977110292856430799

theorem tailTrace_5329585 : CollatzResearch.WordTrace tailWord_5329585 prefixEnd_5329585 304070977110292856430799 := by
  unfold tailWord_5329585
  simp only [CollatzResearch.WordTrace]
  refine ⟨194385934396831240496742209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129590622931220826997828139 194385934396831240496742209)
  ·
    refine ⟨145789450797623430372556657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194385934396831240496742209 145789450797623430372556657)
    ·
      refine ⟨109342088098217572779417493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145789450797623430372556657 109342088098217572779417493)
      ·
        refine ⟨5125410379603948724035195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 109342088098217572779417493 5125410379603948724035195)
        ·
          refine ⟨7688115569405923086052793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5125410379603948724035195 7688115569405923086052793)
          ·
            refine ⟨5766086677054442314539595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7688115569405923086052793 5766086677054442314539595)
            ·
              refine ⟨8649130015581663471809393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5766086677054442314539595 8649130015581663471809393)
              ·
                refine ⟨6486847511686247603857045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8649130015581663471809393 6486847511686247603857045)
                ·
                  refine ⟨304070977110292856430799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6486847511686247603857045 304070977110292856430799)
                  ·
                    rfl

theorem cell23_5329585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 6].length) (baseStart_5329585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329585 prefixEnd_5329585 := by exact prefixLift 5329585
  have htrace : WordTrace (prefixWord ++ tailWord_5329585) baseStart_5329585 baseEnd_5329585 := by
    simpa [prefixWord, tailWord_5329585, baseEnd_5329585] using wordTrace_append hprefix tailTrace_5329585
  have hstable : (prefixWord ++ tailWord_5329585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329585).length < 2 ^ (prefixWord ++ tailWord_5329585).sum := by decide
  have hdescent : baseEnd_5329585 < baseStart_5329585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329662 : List Nat := [4, 2, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_5329662 : Nat := 118140960795 + 5329662 * 2 ^ 59
def prefixEnd_5329662 : Nat := 4983230072969 + 3 ^ 40 * 5329662 * 2
def baseEnd_5329662 : Nat := 912226110667677302204779

theorem tailTrace_5329662 : CollatzResearch.WordTrace tailWord_5329662 prefixEnd_5329662 912226110667677302204779 := by
  unfold tailWord_5329662
  simp only [CollatzResearch.WordTrace]
  refine ⟨24298592852194035330911905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129592495211701521764863493 24298592852194035330911905)
  ·
    refine ⟨18223944639145526498183929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24298592852194035330911905 18223944639145526498183929)
    ·
      refine ⟨13667958479359144873637947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18223944639145526498183929 13667958479359144873637947)
      ·
        refine ⟨20501937719038717310456921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13667958479359144873637947 20501937719038717310456921)
        ·
          refine ⟨15376453289279037982842691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20501937719038717310456921 15376453289279037982842691)
          ·
            refine ⟨23064679933918556974264037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15376453289279037982842691 23064679933918556974264037)
            ·
              refine ⟨4324627487609729432674507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23064679933918556974264037 4324627487609729432674507)
              ·
                refine ⟨6486941231414594149011761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4324627487609729432674507 6486941231414594149011761)
                ·
                  refine ⟨4865205923560945611758821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6486941231414594149011761 4865205923560945611758821)
                  ·
                    refine ⟨912226110667677302204779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4865205923560945611758821 912226110667677302204779)
                    ·
                      rfl

theorem cell23_5329662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_5329662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329662 prefixEnd_5329662 := by exact prefixLift 5329662
  have htrace : WordTrace (prefixWord ++ tailWord_5329662) baseStart_5329662 baseEnd_5329662 := by
    simpa [prefixWord, tailWord_5329662, baseEnd_5329662] using wordTrace_append hprefix tailTrace_5329662
  have hstable : (prefixWord ++ tailWord_5329662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329662).length < 2 ^ (prefixWord ++ tailWord_5329662).sum := by decide
  have hdescent : baseEnd_5329662 < baseStart_5329662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329668 : List Nat := [2, 3, 2, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_5329668 : Nat := 118140960795 + 5329668 * 2 ^ 59
def prefixEnd_5329668 : Nat := 4983230072969 + 3 ^ 40 * 5329668 * 2
def baseEnd_5329668 : Nat := 2736681412886958883139309

theorem tailTrace_5329668 : CollatzResearch.WordTrace tailWord_5329668 prefixEnd_5329668 2736681412886958883139309 := by
  unfold tailWord_5329668
  simp only [CollatzResearch.WordTrace]
  refine ⟨97194480827765272836006829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129592641103687030448009105 97194480827765272836006829)
  ·
    refine ⟨36447930310411977313502561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97194480827765272836006829 36447930310411977313502561)
    ·
      refine ⟨27335947732808982985126921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36447930310411977313502561 27335947732808982985126921)
      ·
        refine ⟨20501960799606737238845191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27335947732808982985126921 20501960799606737238845191)
        ·
          refine ⟨30752941199410105858267787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20501960799606737238845191 30752941199410105858267787)
          ·
            refine ⟨46129411799115158787401681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30752941199410105858267787 46129411799115158787401681)
            ·
              refine ⟨34597058849336369090551261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46129411799115158787401681 34597058849336369090551261)
              ·
                refine ⟨12973897068501138408956723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34597058849336369090551261 12973897068501138408956723)
                ·
                  refine ⟨19460845602751707613435085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12973897068501138408956723 19460845602751707613435085)
                  ·
                    refine ⟨7297817101031890355038157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19460845602751707613435085 7297817101031890355038157)
                    ·
                      refine ⟨2736681412886958883139309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7297817101031890355038157 2736681412886958883139309)
                      ·
                        rfl

theorem cell23_5329668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_5329668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329668 prefixEnd_5329668 := by exact prefixLift 5329668
  have htrace : WordTrace (prefixWord ++ tailWord_5329668) baseStart_5329668 baseEnd_5329668 := by
    simpa [prefixWord, tailWord_5329668, baseEnd_5329668] using wordTrace_append hprefix tailTrace_5329668
  have hstable : (prefixWord ++ tailWord_5329668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329668).length < 2 ^ (prefixWord ++ tailWord_5329668).sum := by decide
  have hdescent : baseEnd_5329668 < baseStart_5329668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329701 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 2, 6]
def baseStart_5329701 : Nat := 118140960795 + 5329701 * 2 ^ 59
def prefixEnd_5329701 : Nat := 4983230072969 + 3 ^ 40 * 5329701 * 2
def baseEnd_5329701 : Nat := 912232785916185751342219

theorem tailTrace_5329701 : CollatzResearch.WordTrace tailWord_5329701 prefixEnd_5329701 912232785916185751342219 := by
  unfold tailWord_5329701
  simp only [CollatzResearch.WordTrace]
  refine ⟨194390165264410992307964957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129593443509607328205309971 194390165264410992307964957)
  ·
    refine ⟨72896311974154122115486859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194390165264410992307964957 72896311974154122115486859)
    ·
      refine ⟨109344467961231183173230289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72896311974154122115486859 109344467961231183173230289)
      ·
        refine ⟨82008350970923387379922717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109344467961231183173230289 82008350970923387379922717)
        ·
          refine ⟨30753131614096270267471019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82008350970923387379922717 30753131614096270267471019)
          ·
            refine ⟨46129697421144405401206529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30753131614096270267471019 46129697421144405401206529)
            ·
              refine ⟨34597273065858304050904897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46129697421144405401206529 34597273065858304050904897)
              ·
                refine ⟨25947954799393728038178673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34597273065858304050904897 25947954799393728038178673)
                ·
                  refine ⟨19460966099545296028634005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25947954799393728038178673 19460966099545296028634005)
                  ·
                    refine ⟨912232785916185751342219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19460966099545296028634005 912232785916185751342219)
                    ·
                      rfl

theorem cell23_5329701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_5329701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329701 prefixEnd_5329701 := by exact prefixLift 5329701
  have htrace : WordTrace (prefixWord ++ tailWord_5329701) baseStart_5329701 baseEnd_5329701 := by
    simpa [prefixWord, tailWord_5329701, baseEnd_5329701] using wordTrace_append hprefix tailTrace_5329701
  have hstable : (prefixWord ++ tailWord_5329701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329701).length < 2 ^ (prefixWord ++ tailWord_5329701).sum := by decide
  have hdescent : baseEnd_5329701 < baseStart_5329701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329708 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 3, 4, 2]
def baseStart_5329708 : Nat := 118140960795 + 5329708 * 2 ^ 59
def prefixEnd_5329708 : Nat := 4983230072969 + 3 ^ 40 * 5329708 * 2
def baseEnd_5329708 : Nat := 2736701952113138726639125

theorem tailTrace_5329708 : CollatzResearch.WordTrace tailWord_5329708 prefixEnd_5329708 2736701952113138726639125 := by
  unfold tailWord_5329708
  simp only [CollatzResearch.WordTrace]
  refine ⟨97195210287692816251734889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129593613716923755002313185 97195210287692816251734889)
  ·
    refine ⟨72896407715769612188801167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97195210287692816251734889 72896407715769612188801167)
    ·
      refine ⟨109344611573654418283201751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72896407715769612188801167 109344611573654418283201751)
      ·
        refine ⟨164016917360481627424802627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109344611573654418283201751 164016917360481627424802627)
        ·
          refine ⟨246025376040722441137203941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164016917360481627424802627 246025376040722441137203941)
          ·
            refine ⟨46129758007635457713225739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 246025376040722441137203941 46129758007635457713225739)
            ·
              refine ⟨69194637011453186569838609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46129758007635457713225739 69194637011453186569838609)
              ·
                refine ⟨51895977758589889927378957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69194637011453186569838609 51895977758589889927378957)
                ·
                  refine ⟨19460991659471208722767109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51895977758589889927378957 19460991659471208722767109)
                  ·
                    refine ⟨3648935936150851635518833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19460991659471208722767109 3648935936150851635518833)
                    ·
                      refine ⟨2736701952113138726639125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3648935936150851635518833 2736701952113138726639125)
                      ·
                        rfl

theorem cell23_5329708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 4, 2].length) (baseStart_5329708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329708 prefixEnd_5329708 := by exact prefixLift 5329708
  have htrace : WordTrace (prefixWord ++ tailWord_5329708) baseStart_5329708 baseEnd_5329708 := by
    simpa [prefixWord, tailWord_5329708, baseEnd_5329708] using wordTrace_append hprefix tailTrace_5329708
  have hstable : (prefixWord ++ tailWord_5329708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329708).length < 2 ^ (prefixWord ++ tailWord_5329708).sum := by decide
  have hdescent : baseEnd_5329708 < baseStart_5329708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329731 : List Nat := [1, 1, 1, 3, 1, 4, 3, 2, 7]
def baseStart_5329731 : Nat := 118140960795 + 5329731 * 2 ^ 59
def prefixEnd_5329731 : Nat := 4983230072969 + 3 ^ 40 * 5329731 * 2
def baseEnd_5329731 : Nat := 304079306907576904072391

theorem tailTrace_5329731 : CollatzResearch.WordTrace tailWord_5329731 prefixEnd_5329731 304079306907576904072391 := by
  unfold tailWord_5329731
  simp only [CollatzResearch.WordTrace]
  refine ⟨194391259454302307431557047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129594172969534871621038031 194391259454302307431557047)
  ·
    refine ⟨291586889181453461147335571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194391259454302307431557047 291586889181453461147335571)
    ·
      refine ⟨437380333772180191721003357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291586889181453461147335571 437380333772180191721003357)
      ·
        refine ⟨164017625164567571895376259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 437380333772180191721003357 164017625164567571895376259)
        ·
          refine ⟨246026437746851357843064389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164017625164567571895376259 246026437746851357843064389)
          ·
            refine ⟨46129957077534629595574573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 246026437746851357843064389 46129957077534629595574573)
            ·
              refine ⟨17298733904075486098340465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46129957077534629595574573 17298733904075486098340465)
              ·
                refine ⟨12974050428056614573755349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17298733904075486098340465 12974050428056614573755349)
                ·
                  refine ⟨304079306907576904072391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12974050428056614573755349 304079306907576904072391)
                  ·
                    rfl

theorem cell23_5329731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 7].length) (baseStart_5329731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329731 prefixEnd_5329731 := by exact prefixLift 5329731
  have htrace : WordTrace (prefixWord ++ tailWord_5329731) baseStart_5329731 baseEnd_5329731 := by
    simpa [prefixWord, tailWord_5329731, baseEnd_5329731] using wordTrace_append hprefix tailTrace_5329731
  have hstable : (prefixWord ++ tailWord_5329731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329731).length < 2 ^ (prefixWord ++ tailWord_5329731).sum := by decide
  have hdescent : baseEnd_5329731 < baseStart_5329731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329771 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 5]
def baseStart_5329771 : Nat := 118140960795 + 5329771 * 2 ^ 59
def prefixEnd_5329771 : Nat := 4983230072969 + 3 ^ 40 * 5329771 * 2
def baseEnd_5329771 : Nat := 2736734301394371980151335

theorem tailTrace_5329771 : CollatzResearch.WordTrace tailWord_5329771 prefixEnd_5329771 2736734301394371980151335 := by
  unfold tailWord_5329771
  simp only [CollatzResearch.WordTrace]
  refine ⟨194392718374157394263013167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129595145582771596175342111 194392718374157394263013167)
  ·
    refine ⟨291589077561236091394519751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194392718374157394263013167 291589077561236091394519751)
    ·
      refine ⟨437383616341854137091779627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291589077561236091394519751 437383616341854137091779627)
      ·
        refine ⟨656075424512781205637669441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437383616341854137091779627 656075424512781205637669441)
        ·
          refine ⟨492056568384585904228252081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 656075424512781205637669441 492056568384585904228252081)
          ·
            refine ⟨369042426288439428171189061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 492056568384585904228252081 369042426288439428171189061)
            ·
              refine ⟨69195454929082392782097949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 369042426288439428171189061 69195454929082392782097949)
              ·
                refine ⟨25948295598405897293286731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69195454929082392782097949 25948295598405897293286731)
                ·
                  refine ⟨38922443397608845939930097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25948295598405897293286731 38922443397608845939930097)
                  ·
                    refine ⟨29191832548206634454947573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38922443397608845939930097 29191832548206634454947573)
                    ·
                      refine ⟨2736734301394371980151335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29191832548206634454947573 2736734301394371980151335)
                      ·
                        rfl

theorem cell23_5329771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 5].length) (baseStart_5329771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329771 prefixEnd_5329771 := by exact prefixLift 5329771
  have htrace : WordTrace (prefixWord ++ tailWord_5329771) baseStart_5329771 baseEnd_5329771 := by
    simpa [prefixWord, tailWord_5329771, baseEnd_5329771] using wordTrace_append hprefix tailTrace_5329771
  have hstable : (prefixWord ++ tailWord_5329771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329771).length < 2 ^ (prefixWord ++ tailWord_5329771).sum := by decide
  have hdescent : baseEnd_5329771 < baseStart_5329771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329811 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 6]
def baseStart_5329811 : Nat := 118140960795 + 5329811 * 2 ^ 59
def prefixEnd_5329811 : Nat := 4983230072969 + 3 ^ 40 * 5329811 * 2
def baseEnd_5329811 : Nat := 2736754840620551823651151

theorem tailTrace_5329811 : CollatzResearch.WordTrace tailWord_5329811 prefixEnd_5329811 2736754840620551823651151 := by
  unfold tailWord_5329811
  simp only [CollatzResearch.WordTrace]
  refine ⟨194394177294012481094469287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129596118196008320729646191 194394177294012481094469287)
  ·
    refine ⟨291591265941018721641703931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194394177294012481094469287 291591265941018721641703931)
    ·
      refine ⟨437386898911528082462555897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291591265941018721641703931 437386898911528082462555897)
      ·
        refine ⟨328040174183646061846916923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437386898911528082462555897 328040174183646061846916923)
        ·
          refine ⟨492060261275469092770375385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328040174183646061846916923 492060261275469092770375385)
          ·
            refine ⟨369045195956601819577781539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 492060261275469092770375385 369045195956601819577781539)
            ·
              refine ⟨553567793934902729366672309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369045195956601819577781539 553567793934902729366672309)
              ·
                refine ⟨51896980681397130878125529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 553567793934902729366672309 51896980681397130878125529)
                ·
                  refine ⟨38922735511047848158594147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51896980681397130878125529 38922735511047848158594147)
                  ·
                    refine ⟨58384103266571772237891221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38922735511047848158594147 58384103266571772237891221)
                    ·
                      refine ⟨2736754840620551823651151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58384103266571772237891221 2736754840620551823651151)
                      ·
                        rfl

theorem cell23_5329811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_5329811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329811 prefixEnd_5329811 := by exact prefixLift 5329811
  have htrace : WordTrace (prefixWord ++ tailWord_5329811) baseStart_5329811 baseEnd_5329811 := by
    simpa [prefixWord, tailWord_5329811, baseEnd_5329811] using wordTrace_append hprefix tailTrace_5329811
  have hstable : (prefixWord ++ tailWord_5329811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329811).length < 2 ^ (prefixWord ++ tailWord_5329811).sum := by decide
  have hdescent : baseEnd_5329811 < baseStart_5329811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329846 : List Nat := [5, 1, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_5329846 : Nat := 118140960795 + 5329846 * 2 ^ 59
def prefixEnd_5329846 : Nat := 4983230072969 + 3 ^ 40 * 5329846 * 2
def baseEnd_5329846 : Nat := 912257604147819728904497

theorem tailTrace_5329846 : CollatzResearch.WordTrace tailWord_5329846 prefixEnd_5329846 912257604147819728904497 := by
  unfold tailWord_5329846
  simp only [CollatzResearch.WordTrace]
  refine ⟨12149715865555355129499587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129596969232590454714662261 12149715865555355129499587)
  ·
    refine ⟨18224573798333032694249381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12149715865555355129499587 18224573798333032694249381)
    ·
      refine ⟨3417107587187443630171759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18224573798333032694249381 3417107587187443630171759)
      ·
        refine ⟨5125661380781165445257639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3417107587187443630171759 5125661380781165445257639)
        ·
          refine ⟨7688492071171748167886459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5125661380781165445257639 7688492071171748167886459)
          ·
            refine ⟨11532738106757622251829689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7688492071171748167886459 11532738106757622251829689)
            ·
              refine ⟨8649553580068216688872267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11532738106757622251829689 8649553580068216688872267)
              ·
                refine ⟨12974330370102325033308401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8649553580068216688872267 12974330370102325033308401)
                ·
                  refine ⟨9730747777576743774981301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12974330370102325033308401 9730747777576743774981301)
                  ·
                    refine ⟨912257604147819728904497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9730747777576743774981301 912257604147819728904497)
                    ·
                      rfl

theorem cell23_5329846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_5329846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329846 prefixEnd_5329846 := by exact prefixLift 5329846
  have htrace : WordTrace (prefixWord ++ tailWord_5329846) baseStart_5329846 baseEnd_5329846 := by
    simpa [prefixWord, tailWord_5329846, baseEnd_5329846] using wordTrace_append hprefix tailTrace_5329846
  have hstable : (prefixWord ++ tailWord_5329846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329846).length < 2 ^ (prefixWord ++ tailWord_5329846).sum := by decide
  have hdescent : baseEnd_5329846 < baseStart_5329846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329876 : List Nat := [2, 4, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_5329876 : Nat := 118140960795 + 5329876 * 2 ^ 59
def prefixEnd_5329876 : Nat := 4983230072969 + 3 ^ 40 * 5329876 * 2
def baseEnd_5329876 : Nat := 912262738954364689779451

theorem tailTrace_5329876 : CollatzResearch.WordTrace tailWord_5329876 prefixEnd_5329876 912262738954364689779451 := by
  unfold tailWord_5329876
  simp only [CollatzResearch.WordTrace]
  refine ⟨97198274019388498597792741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129597698692517998130390321 97198274019388498597792741)
  ·
    refine ⟨18224676378635343487086139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97198274019388498597792741 18224676378635343487086139)
    ·
      refine ⟨27337014567953015230629209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18224676378635343487086139 27337014567953015230629209)
      ·
        refine ⟨20502760925964761422971907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27337014567953015230629209 20502760925964761422971907)
        ·
          refine ⟨30754141388947142134457861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20502760925964761422971907 30754141388947142134457861)
          ·
            refine ⟨5766401510427589150210849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30754141388947142134457861 5766401510427589150210849)
            ·
              refine ⟨4324801132820691862658137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5766401510427589150210849 4324801132820691862658137)
              ·
                refine ⟨3243600849615518896993603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4324801132820691862658137 3243600849615518896993603)
                ·
                  refine ⟨4865401274423278345490405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3243600849615518896993603 4865401274423278345490405)
                  ·
                    refine ⟨912262738954364689779451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4865401274423278345490405 912262738954364689779451)
                    ·
                      rfl

theorem cell23_5329876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_5329876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329876 prefixEnd_5329876 := by exact prefixLift 5329876
  have htrace : WordTrace (prefixWord ++ tailWord_5329876) baseStart_5329876 baseEnd_5329876 := by
    simpa [prefixWord, tailWord_5329876, baseEnd_5329876] using wordTrace_append hprefix tailTrace_5329876
  have hstable : (prefixWord ++ tailWord_5329876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329876).length < 2 ^ (prefixWord ++ tailWord_5329876).sum := by decide
  have hdescent : baseEnd_5329876 < baseStart_5329876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329885 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 3, 5]
def baseStart_5329885 : Nat := 118140960795 + 5329885 * 2 ^ 59
def prefixEnd_5329885 : Nat := 4983230072969 + 3 ^ 40 * 5329885 * 2
def baseEnd_5329885 : Nat := 912264279396328178041937

theorem tailTrace_5329885 : CollatzResearch.WordTrace tailWord_5329885 prefixEnd_5329885 912264279396328178041937 := by
  unfold tailWord_5329885
  simp only [CollatzResearch.WordTrace]
  refine ⟨194396876295744391732663109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129597917530496261155108739 194396876295744391732663109)
  ·
    refine ⟨36449414305452073449874333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194396876295744391732663109 36449414305452073449874333)
    ·
      refine ⟨13668530364544527543702875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36449414305452073449874333 13668530364544527543702875)
      ·
        refine ⟨20502795546816791315554313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13668530364544527543702875 20502795546816791315554313)
        ·
          refine ⟨15377096660112593486665735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20502795546816791315554313 15377096660112593486665735)
          ·
            refine ⟨23065644990168890229998603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15377096660112593486665735 23065644990168890229998603)
            ·
              refine ⟨34598467485253335344997905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23065644990168890229998603 34598467485253335344997905)
              ·
                refine ⟨25948850613940001508748429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34598467485253335344997905 25948850613940001508748429)
                ·
                  refine ⟨9730818980227500565780661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25948850613940001508748429 9730818980227500565780661)
                  ·
                    refine ⟨912264279396328178041937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9730818980227500565780661 912264279396328178041937)
                    ·
                      rfl

theorem cell23_5329885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_5329885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329885 prefixEnd_5329885 := by exact prefixLift 5329885
  have htrace : WordTrace (prefixWord ++ tailWord_5329885) baseStart_5329885 baseEnd_5329885 := by
    simpa [prefixWord, tailWord_5329885, baseEnd_5329885] using wordTrace_append hprefix tailTrace_5329885
  have hstable : (prefixWord ++ tailWord_5329885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329885).length < 2 ^ (prefixWord ++ tailWord_5329885).sum := by decide
  have hdescent : baseEnd_5329885 < baseStart_5329885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329905 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 3, 1, 4]
def baseStart_5329905 : Nat := 118140960795 + 5329905 * 2 ^ 59
def prefixEnd_5329905 : Nat := 4983230072969 + 3 ^ 40 * 5329905 * 2
def baseEnd_5329905 : Nat := 2736803107802074455875719

theorem tailTrace_5329905 : CollatzResearch.WordTrace tailWord_5329905 prefixEnd_5329905 2736803107802074455875719 := by
  unfold tailWord_5329905
  simp only [CollatzResearch.WordTrace]
  refine ⟨194397605755671935148391169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129598403837114623432260779 194397605755671935148391169)
  ·
    refine ⟨145798204316753951361293377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194397605755671935148391169 145798204316753951361293377)
    ·
      refine ⟨109348653237565463520970033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145798204316753951361293377 109348653237565463520970033)
      ·
        refine ⟨82011489928174097640727525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109348653237565463520970033 82011489928174097640727525)
        ·
          refine ⟨15377154361532643307636411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82011489928174097640727525 15377154361532643307636411)
          ·
            refine ⟨23065731542298964961454617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15377154361532643307636411 23065731542298964961454617)
            ·
              refine ⟨17299298656724223721090963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23065731542298964961454617 17299298656724223721090963)
              ·
                refine ⟨25948947985086335581636445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17299298656724223721090963 25948947985086335581636445)
                ·
                  refine ⟨9730855494407375843113667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25948947985086335581636445 9730855494407375843113667)
                  ·
                    refine ⟨14596283241611063764670501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9730855494407375843113667 14596283241611063764670501)
                    ·
                      refine ⟨2736803107802074455875719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14596283241611063764670501 2736803107802074455875719)
                      ·
                        rfl

theorem cell23_5329905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_5329905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329905 prefixEnd_5329905 := by exact prefixLift 5329905
  have htrace : WordTrace (prefixWord ++ tailWord_5329905) baseStart_5329905 baseEnd_5329905 := by
    simpa [prefixWord, tailWord_5329905, baseEnd_5329905] using wordTrace_append hprefix tailTrace_5329905
  have hstable : (prefixWord ++ tailWord_5329905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329905).length < 2 ^ (prefixWord ++ tailWord_5329905).sum := by decide
  have hdescent : baseEnd_5329905 < baseStart_5329905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329928 : List Nat := [2, 1, 3, 2, 1, 4, 10]
def baseStart_5329928 : Nat := 118140960795 + 5329928 * 2 ^ 59
def prefixEnd_5329928 : Nat := 4983230072969 + 3 ^ 40 * 5329928 * 2
def baseEnd_5329928 : Nat := 33787838492063306986273

theorem tailTrace_5329928 : CollatzResearch.WordTrace tailWord_5329928 prefixEnd_5329928 33787838492063306986273 := by
  unfold tailWord_5329928
  simp only [CollatzResearch.WordTrace]
  refine ⟨97199222317294305038239219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129598963089725740050985625 97199222317294305038239219)
  ·
    refine ⟨145798833475941457557358829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97199222317294305038239219 145798833475941457557358829)
    ·
      refine ⟨54674562553478046584009561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145798833475941457557358829 54674562553478046584009561)
      ·
        refine ⟨41005921915108534938007171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54674562553478046584009561 41005921915108534938007171)
        ·
          refine ⟨61508882872662802407010757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41005921915108534938007171 61508882872662802407010757)
          ·
            refine ⟨11532915538624275451314517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61508882872662802407010757 11532915538624275451314517)
            ·
              refine ⟨33787838492063306986273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11532915538624275451314517 33787838492063306986273)
              ·
                rfl

theorem cell23_5329928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 10].length) (baseStart_5329928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329928 prefixEnd_5329928 := by exact prefixLift 5329928
  have htrace : WordTrace (prefixWord ++ tailWord_5329928) baseStart_5329928 baseEnd_5329928 := by
    simpa [prefixWord, tailWord_5329928, baseEnd_5329928] using wordTrace_append hprefix tailTrace_5329928
  have hstable : (prefixWord ++ tailWord_5329928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329928).length < 2 ^ (prefixWord ++ tailWord_5329928).sum := by decide
  have hdescent : baseEnd_5329928 < baseStart_5329928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329932 : List Nat := [2, 2, 1, 2, 3, 2, 3, 2, 2, 4]
def baseStart_5329932 : Nat := 118140960795 + 5329932 * 2 ^ 59
def prefixEnd_5329932 : Nat := 4983230072969 + 3 ^ 40 * 5329932 * 2
def baseEnd_5329932 : Nat := 912272323926581950079365

theorem tailTrace_5329932 : CollatzResearch.WordTrace tailWord_5329932 prefixEnd_5329932 912272323926581950079365 := by
  unfold tailWord_5329932
  simp only [CollatzResearch.WordTrace]
  refine ⟨97199295263287059379812025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129599060351049412506416033 97199295263287059379812025)
  ·
    refine ⟨72899471447465294534859019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97199295263287059379812025 72899471447465294534859019)
    ·
      refine ⟨109349207171197941802288529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72899471447465294534859019 109349207171197941802288529)
      ·
        refine ⟨82011905378398456351716397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109349207171197941802288529 82011905378398456351716397)
        ·
          refine ⟨30754464516899421131893649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82011905378398456351716397 30754464516899421131893649)
          ·
            refine ⟨23065848387674565848920237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30754464516899421131893649 23065848387674565848920237)
            ·
              refine ⟨8649693145377962193345089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23065848387674565848920237 8649693145377962193345089)
              ·
                refine ⟨6487269859033471645008817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8649693145377962193345089 6487269859033471645008817)
                ·
                  refine ⟨4865452394275103733756613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6487269859033471645008817 4865452394275103733756613)
                  ·
                    refine ⟨912272323926581950079365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4865452394275103733756613 912272323926581950079365)
                    ·
                      rfl

theorem cell23_5329932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_5329932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329932 prefixEnd_5329932 := by exact prefixLift 5329932
  have htrace : WordTrace (prefixWord ++ tailWord_5329932) baseStart_5329932 baseEnd_5329932 := by
    simpa [prefixWord, tailWord_5329932, baseEnd_5329932] using wordTrace_append hprefix tailTrace_5329932
  have hstable : (prefixWord ++ tailWord_5329932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329932).length < 2 ^ (prefixWord ++ tailWord_5329932).sum := by decide
  have hdescent : baseEnd_5329932 < baseStart_5329932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329949 : List Nat := [1, 4, 2, 2, 4, 1, 1, 1, 1, 6]
def baseStart_5329949 : Nat := 118140960795 + 5329949 * 2 ^ 59
def prefixEnd_5329949 : Nat := 4983230072969 + 3 ^ 40 * 5329949 * 2
def baseEnd_5329949 : Nat := 912275233650290761241839

theorem tailTrace_5329949 : CollatzResearch.WordTrace tailWord_5329949 prefixEnd_5329949 912275233650290761241839 := by
  unfold tailWord_5329949
  simp only [CollatzResearch.WordTrace]
  refine ⟨194399210567512530662992901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129599473711675020441995267 194399210567512530662992901)
  ·
    refine ⟨36449851981408599499311169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194399210567512530662992901 36449851981408599499311169)
    ·
      refine ⟨27337388986056449624483377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36449851981408599499311169 27337388986056449624483377)
      ·
        refine ⟨20503041739542337218362533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27337388986056449624483377 20503041739542337218362533)
        ·
          refine ⟨3844320326164188228442975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20503041739542337218362533 3844320326164188228442975)
          ·
            refine ⟨5766480489246282342664463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3844320326164188228442975 5766480489246282342664463)
            ·
              refine ⟨8649720733869423513996695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5766480489246282342664463 8649720733869423513996695)
              ·
                refine ⟨12974581100804135270995043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8649720733869423513996695 12974581100804135270995043)
                ·
                  refine ⟨19461871651206202906492565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12974581100804135270995043 19461871651206202906492565)
                  ·
                    refine ⟨912275233650290761241839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19461871651206202906492565 912275233650290761241839)
                    ·
                      rfl

theorem cell23_5329949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_5329949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329949 prefixEnd_5329949 := by exact prefixLift 5329949
  have htrace : WordTrace (prefixWord ++ tailWord_5329949) baseStart_5329949 baseEnd_5329949 := by
    simpa [prefixWord, tailWord_5329949, baseEnd_5329949] using wordTrace_append hprefix tailTrace_5329949
  have hstable : (prefixWord ++ tailWord_5329949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329949).length < 2 ^ (prefixWord ++ tailWord_5329949).sum := by decide
  have hdescent : baseEnd_5329949 < baseStart_5329949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329952 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 1, 1, 6]
def baseStart_5329952 : Nat := 118140960795 + 5329952 * 2 ^ 59
def prefixEnd_5329952 : Nat := 4983230072969 + 3 ^ 40 * 5329952 * 2
def baseEnd_5329952 : Nat := 2736827241392835771988003

theorem tailTrace_5329952 : CollatzResearch.WordTrace tailWord_5329952 prefixEnd_5329952 2736827241392835771988003 := by
  unfold tailWord_5329952
  simp only [CollatzResearch.WordTrace]
  refine ⟨97199659993250831087676055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129599546657667774783568073 97199659993250831087676055)
  ·
    refine ⟨145799489989876246631514083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97199659993250831087676055 145799489989876246631514083)
    ·
      refine ⟨218699234984814369947271125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145799489989876246631514083 218699234984814369947271125)
      ·
        refine ⟨5125763319956586795639167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 218699234984814369947271125 5125763319956586795639167)
        ·
          refine ⟨7688644979934880193458751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5125763319956586795639167 7688644979934880193458751)
          ·
            refine ⟨11532967469902320290188127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7688644979934880193458751 11532967469902320290188127)
            ·
              refine ⟨17299451204853480435282191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11532967469902320290188127 17299451204853480435282191)
              ·
                refine ⟨25949176807280220652923287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17299451204853480435282191 25949176807280220652923287)
                ·
                  refine ⟨38923765210920330979384931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25949176807280220652923287 38923765210920330979384931)
                  ·
                    refine ⟨58385647816380496469077397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38923765210920330979384931 58385647816380496469077397)
                    ·
                      refine ⟨2736827241392835771988003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58385647816380496469077397 2736827241392835771988003)
                      ·
                        rfl

theorem cell23_5329952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_5329952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329952 prefixEnd_5329952 := by exact prefixLift 5329952
  have htrace : WordTrace (prefixWord ++ tailWord_5329952) baseStart_5329952 baseEnd_5329952 := by
    simpa [prefixWord, tailWord_5329952, baseEnd_5329952] using wordTrace_append hprefix tailTrace_5329952
  have hstable : (prefixWord ++ tailWord_5329952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329952).length < 2 ^ (prefixWord ++ tailWord_5329952).sum := by decide
  have hdescent : baseEnd_5329952 < baseStart_5329952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329959 : List Nat := [1, 1, 7, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_5329959 : Nat := 118140960795 + 5329959 * 2 ^ 59
def prefixEnd_5329959 : Nat := 4983230072969 + 3 ^ 40 * 5329959 * 2
def baseEnd_5329959 : Nat := 2736830835757417244600471

theorem tailTrace_5329959 : CollatzResearch.WordTrace tailWord_5329959 prefixEnd_5329959 2736830835757417244600471 := by
  unfold tailWord_5329959
  simp only [CollatzResearch.WordTrace]
  refine ⟨194399575297476302370856931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129599716864984201580571287 194399575297476302370856931)
  ·
    refine ⟨291599362946214453556285397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194399575297476302370856931 291599362946214453556285397)
    ·
      refine ⟨6834360069051901255225439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 291599362946214453556285397 6834360069051901255225439)
      ·
        refine ⟨10251540103577851882838159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6834360069051901255225439 10251540103577851882838159)
        ·
          refine ⟨15377310155366777824257239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10251540103577851882838159 15377310155366777824257239)
          ·
            refine ⟨23065965233050166736385859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15377310155366777824257239 23065965233050166736385859)
            ·
              refine ⟨34598947849575250104578789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23065965233050166736385859 34598947849575250104578789)
              ·
                refine ⟨6487302721795359394608523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34598947849575250104578789 6487302721795359394608523)
                ·
                  refine ⟨9730954082693039091912785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6487302721795359394608523 9730954082693039091912785)
                  ·
                    refine ⟨7298215562019779318934589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9730954082693039091912785 7298215562019779318934589)
                    ·
                      refine ⟨2736830835757417244600471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7298215562019779318934589 2736830835757417244600471)
                      ·
                        rfl

theorem cell23_5329959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_5329959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329959 prefixEnd_5329959 := by exact prefixLift 5329959
  have htrace : WordTrace (prefixWord ++ tailWord_5329959) baseStart_5329959 baseEnd_5329959 := by
    simpa [prefixWord, tailWord_5329959, baseEnd_5329959] using wordTrace_append hprefix tailTrace_5329959
  have hstable : (prefixWord ++ tailWord_5329959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329959).length < 2 ^ (prefixWord ++ tailWord_5329959).sum := by decide
  have hdescent : baseEnd_5329959 < baseStart_5329959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329968 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 5]
def baseStart_5329968 : Nat := 118140960795 + 5329968 * 2 ^ 59
def prefixEnd_5329968 : Nat := 4983230072969 + 3 ^ 40 * 5329968 * 2
def baseEnd_5329968 : Nat := 2736835457083307709387929

theorem tailTrace_5329968 : CollatzResearch.WordTrace tailWord_5329968 prefixEnd_5329968 2736835457083307709387929 := by
  unfold tailWord_5329968
  simp only [CollatzResearch.WordTrace]
  refine ⟨97199951777221848453967279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129599935702962464605289705 97199951777221848453967279)
  ·
    refine ⟨145799927665832772680950919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97199951777221848453967279 145799927665832772680950919)
    ·
      refine ⟨218699891498749159021426379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145799927665832772680950919 218699891498749159021426379)
      ·
        refine ⟨328049837248123738532139569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218699891498749159021426379 328049837248123738532139569)
        ·
          refine ⟨246037377936092803899104677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328049837248123738532139569 246037377936092803899104677)
          ·
            refine ⟨46132008363017400731082127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 246037377936092803899104677 46132008363017400731082127)
            ·
              refine ⟨69198012544526101096623191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46132008363017400731082127 69198012544526101096623191)
              ·
                refine ⟨103797018816789151644934787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69198012544526101096623191 103797018816789151644934787)
                ·
                  refine ⟨155695528225183727467402181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103797018816789151644934787 155695528225183727467402181)
                  ·
                    refine ⟨29192911542221948900137909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 155695528225183727467402181 29192911542221948900137909)
                    ·
                      refine ⟨2736835457083307709387929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29192911542221948900137909 2736835457083307709387929)
                      ·
                        rfl

theorem cell23_5329968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_5329968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329968 prefixEnd_5329968 := by exact prefixLift 5329968
  have htrace : WordTrace (prefixWord ++ tailWord_5329968) baseStart_5329968 baseEnd_5329968 := by
    simpa [prefixWord, tailWord_5329968, baseEnd_5329968] using wordTrace_append hprefix tailTrace_5329968
  have hstable : (prefixWord ++ tailWord_5329968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329968).length < 2 ^ (prefixWord ++ tailWord_5329968).sum := by decide
  have hdescent : baseEnd_5329968 < baseStart_5329968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5329995 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 2, 8, 2]
def baseStart_5329995 : Nat := 118140960795 + 5329995 * 2 ^ 59
def prefixEnd_5329995 : Nat := 4983230072969 + 3 ^ 40 * 5329995 * 2
def baseEnd_5329995 : Nat := 2736849321060979103750305

theorem tailTrace_5329995 : CollatzResearch.WordTrace tailWord_5329995 prefixEnd_5329995 2736849321060979103750305 := by
  unfold tailWord_5329995
  simp only [CollatzResearch.WordTrace]
  refine ⟨194400888325345880519167439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129600592216897253679444959 194400888325345880519167439)
  ·
    refine ⟨291601332488018820778751159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194400888325345880519167439 291601332488018820778751159)
    ·
      refine ⟨437401998732028231168126739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291601332488018820778751159 437401998732028231168126739)
      ·
        refine ⟨656102998098042346752190109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437401998732028231168126739 656102998098042346752190109)
        ·
          refine ⟨246038624286765880032071291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 656102998098042346752190109 246038624286765880032071291)
          ·
            refine ⟨369057936430148820048106937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246038624286765880032071291 369057936430148820048106937)
            ·
              refine ⟨276793452322611615036080203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369057936430148820048106937 276793452322611615036080203)
              ·
                refine ⟨415190178483917422554120305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276793452322611615036080203 415190178483917422554120305)
                ·
                  refine ⟨311392633862938066915590229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415190178483917422554120305 311392633862938066915590229)
                  ·
                    refine ⟨3649132428081305471667073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 311392633862938066915590229 3649132428081305471667073)
                    ·
                      refine ⟨2736849321060979103750305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3649132428081305471667073 2736849321060979103750305)
                      ·
                        rfl

theorem cell23_5329995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 8, 2].length) (baseStart_5329995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5329995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5329995 prefixEnd_5329995 := by exact prefixLift 5329995
  have htrace : WordTrace (prefixWord ++ tailWord_5329995) baseStart_5329995 baseEnd_5329995 := by
    simpa [prefixWord, tailWord_5329995, baseEnd_5329995] using wordTrace_append hprefix tailTrace_5329995
  have hstable : (prefixWord ++ tailWord_5329995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5329995).length < 2 ^ (prefixWord ++ tailWord_5329995).sum := by decide
  have hdescent : baseEnd_5329995 < baseStart_5329995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5329995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330029 : List Nat := [1, 5, 1, 1, 2, 3, 1, 2, 1, 4, 2]
def baseStart_5330029 : Nat := 118140960795 + 5330029 * 2 ^ 59
def prefixEnd_5330029 : Nat := 4983230072969 + 3 ^ 40 * 5330029 * 2
def baseEnd_5330029 : Nat := 2736866779403231970725149

theorem tailTrace_5330029 : CollatzResearch.WordTrace tailWord_5330029 prefixEnd_5330029 2736866779403231970725149 := by
  unfold tailWord_5330029
  simp only [CollatzResearch.WordTrace]
  refine ⟨194402128407222704325905141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129601418938148469550603427 194402128407222704325905141)
  ·
    refine ⟨18225199538177128530553607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194402128407222704325905141 18225199538177128530553607)
    ·
      refine ⟨27337799307265692795830411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18225199538177128530553607 27337799307265692795830411)
      ·
        refine ⟨41006698960898539193745617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27337799307265692795830411 41006698960898539193745617)
        ·
          refine ⟨30755024220673904395309213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41006698960898539193745617 30755024220673904395309213)
          ·
            refine ⟨11533134082752714148240955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30755024220673904395309213 11533134082752714148240955)
            ·
              refine ⟨17299701124129071222361433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11533134082752714148240955 17299701124129071222361433)
              ·
                refine ⟨12974775843096803416771075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17299701124129071222361433 12974775843096803416771075)
                ·
                  refine ⟨19462163764645205125156613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12974775843096803416771075 19462163764645205125156613)
                  ·
                    refine ⟨3649155705870975960966865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19462163764645205125156613 3649155705870975960966865)
                    ·
                      refine ⟨2736866779403231970725149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3649155705870975960966865 2736866779403231970725149)
                      ·
                        rfl

theorem cell23_5330029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_5330029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330029 prefixEnd_5330029 := by exact prefixLift 5330029
  have htrace : WordTrace (prefixWord ++ tailWord_5330029) baseStart_5330029 baseEnd_5330029 := by
    simpa [prefixWord, tailWord_5330029, baseEnd_5330029] using wordTrace_append hprefix tailTrace_5330029
  have hstable : (prefixWord ++ tailWord_5330029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330029).length < 2 ^ (prefixWord ++ tailWord_5330029).sum := by decide
  have hdescent : baseEnd_5330029 < baseStart_5330029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330062 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3]
def baseStart_5330062 : Nat := 118140960795 + 5330062 * 2 ^ 59
def prefixEnd_5330062 : Nat := 4983230072969 + 3 ^ 40 * 5330062 * 2
def baseEnd_5330062 : Nat := 2736883724264830341612497

theorem tailTrace_5330062 : CollatzResearch.WordTrace tailWord_5330062 prefixEnd_5330062 2736883724264830341612497 := by
  unfold tailWord_5330062
  simp only [CollatzResearch.WordTrace]
  refine ⟨24300416502012893870232055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129602221344068767307904293 24300416502012893870232055)
  ·
    refine ⟨36450624753019340805348083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24300416502012893870232055 36450624753019340805348083)
    ·
      refine ⟨54675937129529011208022125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36450624753019340805348083 54675937129529011208022125)
      ·
        refine ⟨20503476423573379203008297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54675937129529011208022125 20503476423573379203008297)
        ·
          refine ⟨15377607317680034402256223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20503476423573379203008297 15377607317680034402256223)
          ·
            refine ⟨23066410976520051603384335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15377607317680034402256223 23066410976520051603384335)
            ·
              refine ⟨34599616464780077405076503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23066410976520051603384335 34599616464780077405076503)
              ·
                refine ⟨51899424697170116107614755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34599616464780077405076503 51899424697170116107614755)
                ·
                  refine ⟨77849137045755174161422133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51899424697170116107614755 77849137045755174161422133)
                  ·
                    refine ⟨7298356598039547577633325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77849137045755174161422133 7298356598039547577633325)
                    ·
                      refine ⟨2736883724264830341612497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7298356598039547577633325 2736883724264830341612497)
                      ·
                        rfl

theorem cell23_5330062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_5330062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330062 prefixEnd_5330062 := by exact prefixLift 5330062
  have htrace : WordTrace (prefixWord ++ tailWord_5330062) baseStart_5330062 baseEnd_5330062 := by
    simpa [prefixWord, tailWord_5330062, baseEnd_5330062] using wordTrace_append hprefix tailTrace_5330062
  have hstable : (prefixWord ++ tailWord_5330062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330062).length < 2 ^ (prefixWord ++ tailWord_5330062).sum := by decide
  have hdescent : baseEnd_5330062 < baseStart_5330062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330122 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 1, 4, 3]
def baseStart_5330122 : Nat := 118140960795 + 5330122 * 2 ^ 59
def prefixEnd_5330122 : Nat := 4983230072969 + 3 ^ 40 * 5330122 * 2
def baseEnd_5330122 : Nat := 2736914533104100106862221

theorem tailTrace_5330122 : CollatzResearch.WordTrace tailWord_5330122 prefixEnd_5330122 2736914533104100106862221 := by
  unfold tailWord_5330122
  simp only [CollatzResearch.WordTrace]
  refine ⟨48601380098971445302260155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129603680263923854139360413 48601380098971445302260155)
  ·
    refine ⟨72902070148457167953390233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48601380098971445302260155 72902070148457167953390233)
    ·
      refine ⟨54676552611342875965042675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72902070148457167953390233 54676552611342875965042675)
      ·
        refine ⟨82014828917014313947564013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54676552611342875965042675 82014828917014313947564013)
        ·
          refine ⟨30755560843880367730336505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82014828917014313947564013 30755560843880367730336505)
          ·
            refine ⟨23066670632910275797752379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30755560843880367730336505 23066670632910275797752379)
            ·
              refine ⟨34600005949365413696628569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23066670632910275797752379 34600005949365413696628569)
              ·
                refine ⟨25950004462024060272471427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34600005949365413696628569 25950004462024060272471427)
                ·
                  refine ⟨38925006693036090408707141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25950004462024060272471427 38925006693036090408707141)
                  ·
                    refine ⟨7298438754944266951632589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38925006693036090408707141 7298438754944266951632589)
                    ·
                      refine ⟨2736914533104100106862221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7298438754944266951632589 2736914533104100106862221)
                      ·
                        rfl

theorem cell23_5330122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_5330122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330122 prefixEnd_5330122 := by exact prefixLift 5330122
  have htrace : WordTrace (prefixWord ++ tailWord_5330122) baseStart_5330122 baseEnd_5330122 := by
    simpa [prefixWord, tailWord_5330122, baseEnd_5330122] using wordTrace_append hprefix tailTrace_5330122
  have hstable : (prefixWord ++ tailWord_5330122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330122).length < 2 ^ (prefixWord ++ tailWord_5330122).sum := by decide
  have hdescent : baseEnd_5330122 < baseStart_5330122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330195 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 5]
def baseStart_5330195 : Nat := 118140960795 + 5330195 * 2 ^ 59
def prefixEnd_5330195 : Nat := 4983230072969 + 3 ^ 40 * 5330195 * 2
def baseEnd_5330195 : Nat := 2736952017191878321249385

theorem tailTrace_5330195 : CollatzResearch.WordTrace tailWord_5330195 prefixEnd_5330195 2736952017191878321249385 := by
  unfold tailWord_5330195
  simp only [CollatzResearch.WordTrace]
  refine ⟨194408182924621314676448039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129605455283080876450965359 194408182924621314676448039)
  ·
    refine ⟨291612274386931972014672059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194408182924621314676448039 291612274386931972014672059)
    ·
      refine ⟨437418411580397958022008089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291612274386931972014672059 437418411580397958022008089)
      ·
        refine ⟨328063808685298468516506067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437418411580397958022008089 328063808685298468516506067)
        ·
          refine ⟨492095713027947702774759101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328063808685298468516506067 492095713027947702774759101)
          ·
            refine ⟨184535892385480388540534663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 492095713027947702774759101 184535892385480388540534663)
            ·
              refine ⟨276803838578220582810801995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184535892385480388540534663 276803838578220582810801995)
              ·
                refine ⟨415205757867330874216202993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276803838578220582810801995 415205757867330874216202993)
                ·
                  refine ⟨311404318400498155662152245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415205757867330874216202993 311404318400498155662152245)
                  ·
                    refine ⟨29194154850046702093326773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 311404318400498155662152245 29194154850046702093326773)
                    ·
                      refine ⟨2736952017191878321249385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29194154850046702093326773 2736952017191878321249385)
                      ·
                        rfl

theorem cell23_5330195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_5330195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330195 prefixEnd_5330195 := by exact prefixLift 5330195
  have htrace : WordTrace (prefixWord ++ tailWord_5330195) baseStart_5330195 baseEnd_5330195 := by
    simpa [prefixWord, tailWord_5330195, baseEnd_5330195] using wordTrace_append hprefix tailTrace_5330195
  have hstable : (prefixWord ++ tailWord_5330195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330195).length < 2 ^ (prefixWord ++ tailWord_5330195).sum := by decide
  have hdescent : baseEnd_5330195 < baseStart_5330195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330202 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 3, 6]
def baseStart_5330202 : Nat := 118140960795 + 5330202 * 2 ^ 59
def prefixEnd_5330202 : Nat := 4983230072969 + 3 ^ 40 * 5330202 * 2
def baseEnd_5330202 : Nat := 912318537185486597953951

theorem tailTrace_5330202 : CollatzResearch.WordTrace tailWord_5330202 prefixEnd_5330202 912318537185486597953951 := by
  unfold tailWord_5330202
  simp only [CollatzResearch.WordTrace]
  refine ⟨48602109558898988717988215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129605625490397303247968573 48602109558898988717988215)
  ·
    refine ⟨72903164338348483076982323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48602109558898988717988215 72903164338348483076982323)
    ·
      refine ⟨109354746507522724615473485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72903164338348483076982323 109354746507522724615473485)
      ·
        refine ⟨41008029940321021730802557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109354746507522724615473485 41008029940321021730802557)
        ·
          refine ⟨15378011227620383149050959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41008029940321021730802557 15378011227620383149050959)
          ·
            refine ⟨23067016841430574723576439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15378011227620383149050959 23067016841430574723576439)
            ·
              refine ⟨34600525262145862085364659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23067016841430574723576439 34600525262145862085364659)
              ·
                refine ⟨51900787893218793128046989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34600525262145862085364659 51900787893218793128046989)
                ·
                  refine ⟨19462795459957047423017621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51900787893218793128046989 19462795459957047423017621)
                  ·
                    refine ⟨912318537185486597953951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19462795459957047423017621 912318537185486597953951)
                    ·
                      rfl

theorem cell23_5330202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_5330202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330202 prefixEnd_5330202 := by exact prefixLift 5330202
  have htrace : WordTrace (prefixWord ++ tailWord_5330202) baseStart_5330202 baseEnd_5330202 := by
    simpa [prefixWord, tailWord_5330202, baseEnd_5330202] using wordTrace_append hprefix tailTrace_5330202
  have hstable : (prefixWord ++ tailWord_5330202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330202).length < 2 ^ (prefixWord ++ tailWord_5330202).sum := by decide
  have hdescent : baseEnd_5330202 < baseStart_5330202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330229 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_5330229 : Nat := 118140960795 + 5330229 * 2 ^ 59
def prefixEnd_5330229 : Nat := 4983230072969 + 3 ^ 40 * 5330229 * 2
def baseEnd_5330229 : Nat := 2736969475534131188224229

theorem tailTrace_5330229 : CollatzResearch.WordTrace tailWord_5330229 prefixEnd_5330229 2736969475534131188224229 := by
  unfold tailWord_5330229
  simp only [CollatzResearch.WordTrace]
  refine ⟨194409423006498138483185741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129606282004332092322123827 194409423006498138483185741)
  ·
    refine ⟨72903533627436801931194653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194409423006498138483185741 72903533627436801931194653)
    ·
      refine ⟨27338825110288800724197995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72903533627436801931194653 27338825110288800724197995)
      ·
        refine ⟨41008237665433201086296993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27338825110288800724197995 41008237665433201086296993)
        ·
          refine ⟨30756178249074900814722745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41008237665433201086296993 30756178249074900814722745)
          ·
            refine ⟨23067133686806175611042059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30756178249074900814722745 23067133686806175611042059)
            ·
              refine ⟨34600700530209263416563089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23067133686806175611042059 34600700530209263416563089)
              ·
                refine ⟨25950525397656947562422317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34600700530209263416563089 25950525397656947562422317)
                ·
                  refine ⟨9731447024121355335908369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25950525397656947562422317 9731447024121355335908369)
                  ·
                    refine ⟨7298585268091016501931277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9731447024121355335908369 7298585268091016501931277)
                    ·
                      refine ⟨2736969475534131188224229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7298585268091016501931277 2736969475534131188224229)
                      ·
                        rfl

theorem cell23_5330229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_5330229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330229 prefixEnd_5330229 := by exact prefixLift 5330229
  have htrace : WordTrace (prefixWord ++ tailWord_5330229) baseStart_5330229 baseEnd_5330229 := by
    simpa [prefixWord, tailWord_5330229, baseEnd_5330229] using wordTrace_append hprefix tailTrace_5330229
  have hstable : (prefixWord ++ tailWord_5330229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330229).length < 2 ^ (prefixWord ++ tailWord_5330229).sum := by decide
  have hdescent : baseEnd_5330229 < baseStart_5330229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330239 : List Nat := [1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 4]
def baseStart_5330239 : Nat := 118140960795 + 5330239 * 2 ^ 59
def prefixEnd_5330239 : Nat := 4983230072969 + 3 ^ 40 * 5330239 * 2
def baseEnd_5330239 : Nat := 2736974610340676149099183

theorem tailTrace_5330239 : CollatzResearch.WordTrace tailWord_5330239 prefixEnd_5330239 2736974610340676149099183 := by
  unfold tailWord_5330239
  simp only [CollatzResearch.WordTrace]
  refine ⟨194409787736461910191049771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129606525157641273460699847 194409787736461910191049771)
  ·
    refine ⟨291614681604692865286574657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194409787736461910191049771 291614681604692865286574657)
    ·
      refine ⟨218711011203519648964930993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291614681604692865286574657 218711011203519648964930993)
      ·
        refine ⟨164033258402639736723698245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218711011203519648964930993 164033258402639736723698245)
        ·
          refine ⟨30756235950494950635693421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164033258402639736723698245 30756235950494950635693421)
          ·
            refine ⟨11533588481435606488385033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30756235950494950635693421 11533588481435606488385033)
            ·
              refine ⟨8650191361076704866288775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11533588481435606488385033 8650191361076704866288775)
              ·
                refine ⟨12975287041615057299433163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8650191361076704866288775 12975287041615057299433163)
                ·
                  refine ⟨19462930562422585949149745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12975287041615057299433163 19462930562422585949149745)
                  ·
                    refine ⟨14597197921816939461862309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19462930562422585949149745 14597197921816939461862309)
                    ·
                      refine ⟨2736974610340676149099183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14597197921816939461862309 2736974610340676149099183)
                      ·
                        rfl

theorem cell23_5330239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_5330239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330239 prefixEnd_5330239 := by exact prefixLift 5330239
  have htrace : WordTrace (prefixWord ++ tailWord_5330239) baseStart_5330239 baseEnd_5330239 := by
    simpa [prefixWord, tailWord_5330239, baseEnd_5330239] using wordTrace_append hprefix tailTrace_5330239
  have hstable : (prefixWord ++ tailWord_5330239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330239).length < 2 ^ (prefixWord ++ tailWord_5330239).sum := by decide
  have hdescent : baseEnd_5330239 < baseStart_5330239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330259 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 4, 1, 3]
def baseStart_5330259 : Nat := 118140960795 + 5330259 * 2 ^ 59
def prefixEnd_5330259 : Nat := 4983230072969 + 3 ^ 40 * 5330259 * 2
def baseEnd_5330259 : Nat := 2736984879953766070849091

theorem tailTrace_5330259 : CollatzResearch.WordTrace tailWord_5330259 prefixEnd_5330259 2736984879953766070849091 := by
  unfold tailWord_5330259
  simp only [CollatzResearch.WordTrace]
  refine ⟨194410517196389453606777831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129607011464259635737851887 194410517196389453606777831)
  ·
    refine ⟨291615775794584180410166747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194410517196389453606777831 291615775794584180410166747)
    ·
      refine ⟨437423663691876270615250121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291615775794584180410166747 437423663691876270615250121)
      ·
        refine ⟨328067747768907202961437591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437423663691876270615250121 328067747768907202961437591)
        ·
          refine ⟨492101621653360804442156387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328067747768907202961437591 492101621653360804442156387)
          ·
            refine ⟨738152432480041206663234581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492101621653360804442156387 738152432480041206663234581)
            ·
              refine ⟨34600895272501931562339121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 738152432480041206663234581 34600895272501931562339121)
              ·
                refine ⟨25950671454376448671754341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34600895272501931562339121 25950671454376448671754341)
                ·
                  refine ⟨4865750897695584125953939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25950671454376448671754341 4865750897695584125953939)
                  ·
                    refine ⟨7298626346543376188930909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4865750897695584125953939 7298626346543376188930909)
                    ·
                      refine ⟨2736984879953766070849091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7298626346543376188930909 2736984879953766070849091)
                      ·
                        rfl

theorem cell23_5330259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 1, 3].length) (baseStart_5330259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330259 prefixEnd_5330259 := by exact prefixLift 5330259
  have htrace : WordTrace (prefixWord ++ tailWord_5330259) baseStart_5330259 baseEnd_5330259 := by
    simpa [prefixWord, tailWord_5330259, baseEnd_5330259] using wordTrace_append hprefix tailTrace_5330259
  have hstable : (prefixWord ++ tailWord_5330259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330259).length < 2 ^ (prefixWord ++ tailWord_5330259).sum := by decide
  have hdescent : baseEnd_5330259 < baseStart_5330259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330260 : List Nat := [2, 4, 1, 1, 2, 1, 4, 3, 1, 2, 2]
def baseStart_5330260 : Nat := 118140960795 + 5330260 * 2 ^ 59
def prefixEnd_5330260 : Nat := 4983230072969 + 3 ^ 40 * 5330260 * 2
def baseEnd_5330260 : Nat := 2736985393434420566936587

theorem tailTrace_5330260 : CollatzResearch.WordTrace tailWord_5330260 prefixEnd_5330260 2736985393434420566936587 := by
  unfold tailWord_5330260
  simp only [CollatzResearch.WordTrace]
  refine ⟨97205276834692915388782117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129607035779590553851709489 97205276834692915388782117)
  ·
    refine ⟨18225989406504921635396647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97205276834692915388782117 18225989406504921635396647)
    ·
      refine ⟨27338984109757382453094971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18225989406504921635396647 27338984109757382453094971)
      ·
        refine ⟨41008476164636073679642457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27338984109757382453094971 41008476164636073679642457)
        ·
          refine ⟨30756357123477055259731843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41008476164636073679642457 30756357123477055259731843)
          ·
            refine ⟨46134535685215582889597765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30756357123477055259731843 46134535685215582889597765)
            ·
              refine ⟨8650225440977921791799581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46134535685215582889597765 8650225440977921791799581)
              ·
                refine ⟨3243834540366720671924843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8650225440977921791799581 3243834540366720671924843)
                ·
                  refine ⟨4865751810550081007887265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3243834540366720671924843 4865751810550081007887265)
                  ·
                    refine ⟨3649313857912560755915449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4865751810550081007887265 3649313857912560755915449)
                    ·
                      refine ⟨2736985393434420566936587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3649313857912560755915449 2736985393434420566936587)
                      ·
                        rfl

theorem cell23_5330260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_5330260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330260 prefixEnd_5330260 := by exact prefixLift 5330260
  have htrace : WordTrace (prefixWord ++ tailWord_5330260) baseStart_5330260 baseEnd_5330260 := by
    simpa [prefixWord, tailWord_5330260, baseEnd_5330260] using wordTrace_append hprefix tailTrace_5330260
  have hstable : (prefixWord ++ tailWord_5330260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330260).length < 2 ^ (prefixWord ++ tailWord_5330260).sum := by decide
  have hdescent : baseEnd_5330260 < baseStart_5330260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330263 : List Nat := [1, 1, 3, 2, 3, 4, 2, 1, 1, 2, 3]
def baseStart_5330263 : Nat := 118140960795 + 5330263 * 2 ^ 59
def prefixEnd_5330263 : Nat := 4983230072969 + 3 ^ 40 * 5330263 * 2
def baseEnd_5330263 : Nat := 2736986933876384055199073

theorem tailTrace_5330263 : CollatzResearch.WordTrace tailWord_5330263 prefixEnd_5330263 2736986933876384055199073 := by
  unfold tailWord_5330263
  simp only [CollatzResearch.WordTrace]
  refine ⟨194410663088374962289923443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129607108725583308193282295 194410663088374962289923443)
  ·
    refine ⟨291615994632562443434885165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194410663088374962289923443 291615994632562443434885165)
    ·
      refine ⟨109355997987210916288081937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291615994632562443434885165 109355997987210916288081937)
      ·
        refine ⟨82016998490408187216061453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109355997987210916288081937 82016998490408187216061453)
        ·
          refine ⟨30756374433903070206023045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82016998490408187216061453 30756374433903070206023045)
          ·
            refine ⟨5766820206356825663629321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30756374433903070206023045 5766820206356825663629321)
            ·
              refine ⟨4325115154767619247721991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5766820206356825663629321 4325115154767619247721991)
              ·
                refine ⟨6487672732151428871582987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4325115154767619247721991 6487672732151428871582987)
                ·
                  refine ⟨9731509098227143307374481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6487672732151428871582987 9731509098227143307374481)
                  ·
                    refine ⟨7298631823670357480530861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9731509098227143307374481 7298631823670357480530861)
                    ·
                      refine ⟨2736986933876384055199073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7298631823670357480530861 2736986933876384055199073)
                      ·
                        rfl

theorem cell23_5330263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_5330263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330263 prefixEnd_5330263 := by exact prefixLift 5330263
  have htrace : WordTrace (prefixWord ++ tailWord_5330263) baseStart_5330263 baseEnd_5330263 := by
    simpa [prefixWord, tailWord_5330263, baseEnd_5330263] using wordTrace_append hprefix tailTrace_5330263
  have hstable : (prefixWord ++ tailWord_5330263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330263).length < 2 ^ (prefixWord ++ tailWord_5330263).sum := by decide
  have hdescent : baseEnd_5330263 < baseStart_5330263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330276 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 4, 1, 3]
def baseStart_5330276 : Nat := 118140960795 + 5330276 * 2 ^ 59
def prefixEnd_5330276 : Nat := 4983230072969 + 3 ^ 40 * 5330276 * 2
def baseEnd_5330276 : Nat := 2736993609124892504336513

theorem tailTrace_5330276 : CollatzResearch.WordTrace tailWord_5330276 prefixEnd_5330276 2736993609124892504336513 := by
  unfold tailWord_5330276
  simp only [CollatzResearch.WordTrace]
  refine ⟨97205568618663932755073341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129607424824885243673431121 97205568618663932755073341)
  ·
    refine ⟨36452088231998974783152503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97205568618663932755073341 36452088231998974783152503)
    ·
      refine ⟨54678132347998462174728755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36452088231998974783152503 54678132347998462174728755)
      ·
        refine ⟨82017198521997693262093133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54678132347998462174728755 82017198521997693262093133)
        ·
          refine ⟨30756449445749134973284925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82017198521997693262093133 30756449445749134973284925)
          ·
            refine ⟨11533668542155925614981847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30756449445749134973284925 11533668542155925614981847)
            ·
              refine ⟨17300502813233888422472771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11533668542155925614981847 17300502813233888422472771)
              ·
                refine ⟨25950754219850832633709157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17300502813233888422472771 25950754219850832633709157)
                ·
                  refine ⟨4865766416222031118820467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25950754219850832633709157 4865766416222031118820467)
                  ·
                    refine ⟨7298649624333046678230701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4865766416222031118820467 7298649624333046678230701)
                    ·
                      refine ⟨2736993609124892504336513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7298649624333046678230701 2736993609124892504336513)
                      ·
                        rfl

theorem cell23_5330276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_5330276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330276 prefixEnd_5330276 := by exact prefixLift 5330276
  have htrace : WordTrace (prefixWord ++ tailWord_5330276) baseStart_5330276 baseEnd_5330276 := by
    simpa [prefixWord, tailWord_5330276, baseEnd_5330276] using wordTrace_append hprefix tailTrace_5330276
  have hstable : (prefixWord ++ tailWord_5330276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330276).length < 2 ^ (prefixWord ++ tailWord_5330276).sum := by decide
  have hdescent : baseEnd_5330276 < baseStart_5330276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330293 : List Nat := [1, 3, 4, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_5330293 : Nat := 118140960795 + 5330293 * 2 ^ 59
def prefixEnd_5330293 : Nat := 4983230072969 + 3 ^ 40 * 5330293 * 2
def baseEnd_5330293 : Nat := 2737002338296018937823935

theorem tailTrace_5330293 : CollatzResearch.WordTrace tailWord_5330293 prefixEnd_5330293 2737002338296018937823935 := by
  unfold tailWord_5330293
  simp only [CollatzResearch.WordTrace]
  refine ⟨194411757278266277413515533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129607838185510851609010355 194411757278266277413515533)
  ·
    refine ⟨72904408979349854030068325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194411757278266277413515533 72904408979349854030068325)
    ·
      refine ⟨13669576683628097630637811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72904408979349854030068325 13669576683628097630637811)
      ·
        refine ⟨20504365025442146445956717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13669576683628097630637811 20504365025442146445956717)
        ·
          refine ⟨7689136884540804917233769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20504365025442146445956717 7689136884540804917233769)
          ·
            refine ⟨5766852663405603687925327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7689136884540804917233769 5766852663405603687925327)
            ·
              refine ⟨8650278995108405531887991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5766852663405603687925327 8650278995108405531887991)
              ·
                refine ⟨12975418492662608297831987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8650278995108405531887991 12975418492662608297831987)
                ·
                  refine ⟨19463127738993912446747981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12975418492662608297831987 19463127738993912446747981)
                  ·
                    refine ⟨7298672902122717167530493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19463127738993912446747981 7298672902122717167530493)
                    ·
                      refine ⟨2737002338296018937823935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7298672902122717167530493 2737002338296018937823935)
                      ·
                        rfl

theorem cell23_5330293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_5330293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330293 prefixEnd_5330293 := by exact prefixLift 5330293
  have htrace : WordTrace (prefixWord ++ tailWord_5330293) baseStart_5330293 baseEnd_5330293 := by
    simpa [prefixWord, tailWord_5330293, baseEnd_5330293] using wordTrace_append hprefix tailTrace_5330293
  have hstable : (prefixWord ++ tailWord_5330293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330293).length < 2 ^ (prefixWord ++ tailWord_5330293).sum := by decide
  have hdescent : baseEnd_5330293 < baseStart_5330293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330306 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_5330306 : Nat := 118140960795 + 5330306 * 2 ^ 59
def prefixEnd_5330306 : Nat := 4983230072969 + 3 ^ 40 * 5330306 * 2
def baseEnd_5330306 : Nat := 2737009013544527386961375

theorem tailTrace_5330306 : CollatzResearch.WordTrace tailWord_5330306 prefixEnd_5330306 2737009013544527386961375 := by
  unfold tailWord_5330306
  simp only [CollatzResearch.WordTrace]
  refine ⟨48603057856804795158434693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129608154284812787089159181 48603057856804795158434693)
  ·
    refine ⟨9113073348150899092206505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48603057856804795158434693 9113073348150899092206505)
    ·
      refine ⟨6834805011113174319154879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9113073348150899092206505 6834805011113174319154879)
      ·
        refine ⟨10252207516669761478732319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6834805011113174319154879 10252207516669761478732319)
        ·
          refine ⟨15378311275004642218098479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10252207516669761478732319 15378311275004642218098479)
          ·
            refine ⟨23067466912506963327147719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15378311275004642218098479 23067466912506963327147719)
            ·
              refine ⟨34601200368760444990721579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23067466912506963327147719 34601200368760444990721579)
              ·
                refine ⟨51901800553140667486082369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34601200368760444990721579 51901800553140667486082369)
                ·
                  refine ⟨38926350414855500614561777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51901800553140667486082369 38926350414855500614561777)
                  ·
                    refine ⟨29194762811141625460921333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38926350414855500614561777 29194762811141625460921333)
                    ·
                      refine ⟨2737009013544527386961375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29194762811141625460921333 2737009013544527386961375)
                      ·
                        rfl

theorem cell23_5330306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_5330306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330306 prefixEnd_5330306 := by exact prefixLift 5330306
  have htrace : WordTrace (prefixWord ++ tailWord_5330306) baseStart_5330306 baseEnd_5330306 := by
    simpa [prefixWord, tailWord_5330306, baseEnd_5330306] using wordTrace_append hprefix tailTrace_5330306
  have hstable : (prefixWord ++ tailWord_5330306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330306).length < 2 ^ (prefixWord ++ tailWord_5330306).sum := by decide
  have hdescent : baseEnd_5330306 < baseStart_5330306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330316 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 6, 2, 2]
def baseStart_5330316 : Nat := 118140960795 + 5330316 * 2 ^ 59
def prefixEnd_5330316 : Nat := 4983230072969 + 3 ^ 40 * 5330316 * 2
def baseEnd_5330316 : Nat := 2737014148351072347836329

theorem tailTrace_5330316 : CollatzResearch.WordTrace tailWord_5330316 prefixEnd_5330316 2737014148351072347836329 := by
  unfold tailWord_5330316
  simp only [CollatzResearch.WordTrace]
  refine ⟨97206298078591476170801401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129608397438121968227735201 97206298078591476170801401)
  ·
    refine ⟨72904723558943607128101051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97206298078591476170801401 72904723558943607128101051)
    ·
      refine ⟨109357085338415410692151577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72904723558943607128101051 109357085338415410692151577)
      ·
        refine ⟨82017814003811558019113683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109357085338415410692151577 82017814003811558019113683)
        ·
          refine ⟨123026721005717337028670525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82017814003811558019113683 123026721005717337028670525)
          ·
            refine ⟨46135020377144001385751447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123026721005717337028670525 46135020377144001385751447)
            ·
              refine ⟨69202530565716002078627171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46135020377144001385751447 69202530565716002078627171)
              ·
                refine ⟨103803795848574003117940757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69202530565716002078627171 103803795848574003117940757)
                ·
                  refine ⟨4865802930401906396153473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103803795848574003117940757 4865802930401906396153473)
                  ·
                    refine ⟨3649352197801429797115105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4865802930401906396153473 3649352197801429797115105)
                    ·
                      refine ⟨2737014148351072347836329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3649352197801429797115105 2737014148351072347836329)
                      ·
                        rfl

theorem cell23_5330316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_5330316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330316 prefixEnd_5330316 := by exact prefixLift 5330316
  have htrace : WordTrace (prefixWord ++ tailWord_5330316) baseStart_5330316 baseEnd_5330316 := by
    simpa [prefixWord, tailWord_5330316, baseEnd_5330316] using wordTrace_append hprefix tailTrace_5330316
  have hstable : (prefixWord ++ tailWord_5330316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330316).length < 2 ^ (prefixWord ++ tailWord_5330316).sum := by decide
  have hdescent : baseEnd_5330316 < baseStart_5330316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330333 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 4, 2, 2]
def baseStart_5330333 : Nat := 118140960795 + 5330333 * 2 ^ 59
def prefixEnd_5330333 : Nat := 4983230072969 + 3 ^ 40 * 5330333 * 2
def baseEnd_5330333 : Nat := 2737022877522198781323751

theorem tailTrace_5330333 : CollatzResearch.WordTrace tailWord_5330333 prefixEnd_5330333 2737022877522198781323751 := by
  unfold tailWord_5330333
  simp only [CollatzResearch.WordTrace]
  refine ⟨194413216198121364244971653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129608810798747576163314435 194413216198121364244971653)
  ·
    refine ⟨36452478037147755795932185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194413216198121364244971653 36452478037147755795932185)
    ·
      refine ⟨27339358527860816846949139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36452478037147755795932185 27339358527860816846949139)
      ·
        refine ⟨41009037791791225270423709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27339358527860816846949139 41009037791791225270423709)
        ·
          refine ⟨15378389171921709476408891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41009037791791225270423709 15378389171921709476408891)
          ·
            refine ⟨23067583757882564214613337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15378389171921709476408891 23067583757882564214613337)
            ·
              refine ⟨17300687818411923160960003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23067583757882564214613337 17300687818411923160960003)
              ·
                refine ⟨25951031727617884741440005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17300687818411923160960003 25951031727617884741440005)
                ·
                  refine ⟨4865818448928353389020001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25951031727617884741440005 4865818448928353389020001)
                  ·
                    refine ⟨3649363836696265041765001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4865818448928353389020001 3649363836696265041765001)
                    ·
                      refine ⟨2737022877522198781323751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3649363836696265041765001 2737022877522198781323751)
                      ·
                        rfl

theorem cell23_5330333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_5330333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330333 prefixEnd_5330333 := by exact prefixLift 5330333
  have htrace : WordTrace (prefixWord ++ tailWord_5330333) baseStart_5330333 baseEnd_5330333 := by
    simpa [prefixWord, tailWord_5330333, baseEnd_5330333] using wordTrace_append hprefix tailTrace_5330333
  have hstable : (prefixWord ++ tailWord_5330333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330333).length < 2 ^ (prefixWord ++ tailWord_5330333).sum := by decide
  have hdescent : baseEnd_5330333 < baseStart_5330333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330344 : List Nat := [2, 1, 6, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_5330344 : Nat := 118140960795 + 5330344 * 2 ^ 59
def prefixEnd_5330344 : Nat := 4983230072969 + 3 ^ 40 * 5330344 * 2
def baseEnd_5330344 : Nat := 2737028525809398238286201

theorem tailTrace_5330344 : CollatzResearch.WordTrace tailWord_5330344 prefixEnd_5330344 2737028525809398238286201 := by
  unfold tailWord_5330344
  simp only [CollatzResearch.WordTrace]
  refine ⟨97206808700540756561811043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129609078267387675415748057 97206808700540756561811043)
  ·
    refine ⟨145810213050811134842716565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97206808700540756561811043 145810213050811134842716565)
    ·
      refine ⟨6834853736756771945752339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 145810213050811134842716565 6834853736756771945752339)
      ·
        refine ⟨10252280605135157918628509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6834853736756771945752339 10252280605135157918628509)
        ·
          refine ⟨3844605226925684219485691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10252280605135157918628509 3844605226925684219485691)
          ·
            refine ⟨5766907840388526329228537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3844605226925684219485691 5766907840388526329228537)
            ·
              refine ⟨4325180880291394746921403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5766907840388526329228537 4325180880291394746921403)
              ·
                refine ⟨6487771320437092120382105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4325180880291394746921403 6487771320437092120382105)
                ·
                  refine ⟨4865828490327819090286579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6487771320437092120382105 4865828490327819090286579)
                  ·
                    refine ⟨7298742735491728635429869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4865828490327819090286579 7298742735491728635429869)
                    ·
                      refine ⟨2737028525809398238286201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7298742735491728635429869 2737028525809398238286201)
                      ·
                        rfl

theorem cell23_5330344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_5330344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330344 prefixEnd_5330344 := by exact prefixLift 5330344
  have htrace : WordTrace (prefixWord ++ tailWord_5330344) baseStart_5330344 baseEnd_5330344 := by
    simpa [prefixWord, tailWord_5330344, baseEnd_5330344] using wordTrace_append hprefix tailTrace_5330344
  have hstable : (prefixWord ++ tailWord_5330344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330344).length < 2 ^ (prefixWord ++ tailWord_5330344).sum := by decide
  have hdescent : baseEnd_5330344 < baseStart_5330344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330352 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 1, 7]
def baseStart_5330352 : Nat := 118140960795 + 5330352 * 2 ^ 59
def prefixEnd_5330352 : Nat := 4983230072969 + 3 ^ 40 * 5330352 * 2
def baseEnd_5330352 : Nat := 912344211218211402328721

theorem tailTrace_5330352 : CollatzResearch.WordTrace tailWord_5330352 prefixEnd_5330352 912344211218211402328721 := by
  unfold tailWord_5330352
  simp only [CollatzResearch.WordTrace]
  refine ⟨97206954592526265244956655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129609272790035020326608873 97206954592526265244956655)
  ·
    refine ⟨145810431888789397867434983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97206954592526265244956655 145810431888789397867434983)
    ·
      refine ⟨218715647833184096801152475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145810431888789397867434983 218715647833184096801152475)
      ·
        refine ⟨328073471749776145201728713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218715647833184096801152475 328073471749776145201728713)
        ·
          refine ⟨246055103812332108901296535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328073471749776145201728713 246055103812332108901296535)
          ·
            refine ⟨369082655718498163351944803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246055103812332108901296535 369082655718498163351944803)
            ·
              refine ⟨553623983577747245027917205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369082655718498163351944803 553623983577747245027917205)
              ·
                refine ⟨25951124230206902110683619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 553623983577747245027917205 25951124230206902110683619)
                ·
                  refine ⟨38926686345310353166025429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25951124230206902110683619 38926686345310353166025429)
                  ·
                    refine ⟨912344211218211402328721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38926686345310353166025429 912344211218211402328721)
                    ·
                      rfl

theorem cell23_5330352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 1, 7].length) (baseStart_5330352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330352 prefixEnd_5330352 := by exact prefixLift 5330352
  have htrace : WordTrace (prefixWord ++ tailWord_5330352) baseStart_5330352 baseEnd_5330352 := by
    simpa [prefixWord, tailWord_5330352, baseEnd_5330352] using wordTrace_append hprefix tailTrace_5330352
  have hstable : (prefixWord ++ tailWord_5330352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330352).length < 2 ^ (prefixWord ++ tailWord_5330352).sum := by decide
  have hdescent : baseEnd_5330352 < baseStart_5330352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330390 : List Nat := [5, 2, 1, 1, 1, 2, 4, 2, 5]
def baseStart_5330390 : Nat := 118140960795 + 5330390 * 2 ^ 59
def prefixEnd_5330390 : Nat := 4983230072969 + 3 ^ 40 * 5330390 * 2
def baseEnd_5330390 : Nat := 304116905102167228701221

theorem tailTrace_5330390 : CollatzResearch.WordTrace tailWord_5330390 prefixEnd_5330390 304116905102167228701221 := by
  unfold tailWord_5330390
  simp only [CollatzResearch.WordTrace]
  refine ⟨12150955947432178936237289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129610196772609908653197749 12150955947432178936237289)
  ·
    refine ⟨9113216960574134202177967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12150955947432178936237289 9113216960574134202177967)
    ·
      refine ⟨13669825440861201303266951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9113216960574134202177967 13669825440861201303266951)
      ·
        refine ⟨20504738161291801954900427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13669825440861201303266951 20504738161291801954900427)
        ·
          refine ⟨30757107241937702932350641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20504738161291801954900427 30757107241937702932350641)
          ·
            refine ⟨23067830431453277199262981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30757107241937702932350641 23067830431453277199262981)
            ·
              refine ⟨4325218205897489474861809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23067830431453277199262981 4325218205897489474861809)
              ·
                refine ⟨3243913654423117106146357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4325218205897489474861809 3243913654423117106146357)
                ·
                  refine ⟨304116905102167228701221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3243913654423117106146357 304116905102167228701221)
                  ·
                    rfl

theorem cell23_5330390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_5330390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330390 prefixEnd_5330390 := by exact prefixLift 5330390
  have htrace : WordTrace (prefixWord ++ tailWord_5330390) baseStart_5330390 baseEnd_5330390 := by
    simpa [prefixWord, tailWord_5330390, baseEnd_5330390] using wordTrace_append hprefix tailTrace_5330390
  have hstable : (prefixWord ++ tailWord_5330390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330390).length < 2 ^ (prefixWord ++ tailWord_5330390).sum := by decide
  have hdescent : baseEnd_5330390 < baseStart_5330390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330416 : List Nat := [2, 1, 1, 1, 3, 5, 1, 2, 3, 4]
def baseStart_5330416 : Nat := 118140960795 + 5330416 * 2 ^ 59
def prefixEnd_5330416 : Nat := 4983230072969 + 3 ^ 40 * 5330416 * 2
def baseEnd_5330416 : Nat := 912355165472173985528623

theorem tailTrace_5330416 : CollatzResearch.WordTrace tailWord_5330416 prefixEnd_5330416 912355165472173985528623 := by
  unfold tailWord_5330416
  simp only [CollatzResearch.WordTrace]
  refine ⟨97208121728410334710121551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129610828971213779613495401 97208121728410334710121551)
  ·
    refine ⟨145812182592615502065182327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97208121728410334710121551 145812182592615502065182327)
    ·
      refine ⟨218718273888923253097773491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145812182592615502065182327 218718273888923253097773491)
      ·
        refine ⟨328077410833384879646660237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218718273888923253097773491 328077410833384879646660237)
        ·
          refine ⟨123029029062519329867497589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 328077410833384879646660237 123029029062519329867497589)
          ·
            refine ⟨11533971474611187175077899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123029029062519329867497589 11533971474611187175077899)
            ·
              refine ⟨17300957211916780762616849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11533971474611187175077899 17300957211916780762616849)
              ·
                refine ⟨12975717908937585571962637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17300957211916780762616849 12975717908937585571962637)
                ·
                  refine ⟨4865894215851594589485989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12975717908937585571962637 4865894215851594589485989)
                  ·
                    refine ⟨912355165472173985528623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4865894215851594589485989 912355165472173985528623)
                    ·
                      rfl

theorem cell23_5330416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 3, 4].length) (baseStart_5330416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330416 prefixEnd_5330416 := by exact prefixLift 5330416
  have htrace : WordTrace (prefixWord ++ tailWord_5330416) baseStart_5330416 baseEnd_5330416 := by
    simpa [prefixWord, tailWord_5330416, baseEnd_5330416] using wordTrace_append hprefix tailTrace_5330416
  have hstable : (prefixWord ++ tailWord_5330416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330416).length < 2 ^ (prefixWord ++ tailWord_5330416).sum := by decide
  have hdescent : baseEnd_5330416 < baseStart_5330416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330446 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 8]
def baseStart_5330446 : Nat := 118140960795 + 5330446 * 2 ^ 59
def prefixEnd_5330446 : Nat := 4983230072969 + 3 ^ 40 * 5330446 * 2
def baseEnd_5330446 : Nat := 304120100092906315467859

theorem tailTrace_5330446 : CollatzResearch.WordTrace tailWord_5330446 prefixEnd_5330446 304120100092906315467859 := by
  unfold tailWord_5330446
  simp only [CollatzResearch.WordTrace]
  refine ⟨24302167205838998067979399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129611558431141323029223461 24302167205838998067979399)
  ·
    refine ⟨36453250808758497101969099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24302167205838998067979399 36453250808758497101969099)
    ·
      refine ⟨54679876213137745652953649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36453250808758497101969099 54679876213137745652953649)
      ·
        refine ⟨41009907159853309239715237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54679876213137745652953649 41009907159853309239715237)
        ·
          refine ⟨7689357592472495482446607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41009907159853309239715237 7689357592472495482446607)
          ·
            refine ⟨11534036388708743223669911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7689357592472495482446607 11534036388708743223669911)
            ·
              refine ⟨17301054583063114835504867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11534036388708743223669911 17301054583063114835504867)
              ·
                refine ⟨25951581874594672253257301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17301054583063114835504867 25951581874594672253257301)
                ·
                  refine ⟨304120100092906315467859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25951581874594672253257301 304120100092906315467859)
                  ·
                    rfl

theorem cell23_5330446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_5330446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330446 prefixEnd_5330446 := by exact prefixLift 5330446
  have htrace : WordTrace (prefixWord ++ tailWord_5330446) baseStart_5330446 baseEnd_5330446 := by
    simpa [prefixWord, tailWord_5330446, baseEnd_5330446] using wordTrace_append hprefix tailTrace_5330446
  have hstable : (prefixWord ++ tailWord_5330446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330446).length < 2 ^ (prefixWord ++ tailWord_5330446).sum := by decide
  have hdescent : baseEnd_5330446 < baseStart_5330446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330506 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 4, 4]
def baseStart_5330506 : Nat := 118140960795 + 5330506 * 2 ^ 59
def prefixEnd_5330506 : Nat := 4983230072969 + 3 ^ 40 * 5330506 * 2
def baseEnd_5330506 : Nat := 912370569891808868153485

theorem tailTrace_5330506 : CollatzResearch.WordTrace tailWord_5330506 prefixEnd_5330506 912370569891808868153485 := by
  unfold tailWord_5330506
  simp only [CollatzResearch.WordTrace]
  refine ⟨48604881506623653697754843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129613017350996409860679581 48604881506623653697754843)
  ·
    refine ⟨72907322259935480546632265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48604881506623653697754843 72907322259935480546632265)
    ·
      refine ⟨54680491694951610409974199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72907322259935480546632265 54680491694951610409974199)
      ·
        refine ⟨82020737542427415614961299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54680491694951610409974199 82020737542427415614961299)
        ·
          refine ⟨123031106313641123422441949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82020737542427415614961299 123031106313641123422441949)
          ·
            refine ⟨46136664867615421283415731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123031106313641123422441949 46136664867615421283415731)
            ·
              refine ⟨69204997301423131925123597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46136664867615421283415731 69204997301423131925123597)
              ·
                refine ⟨25951873988033674471921349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69204997301423131925123597 25951873988033674471921349)
                ·
                  refine ⟨4865976372756313963485253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25951873988033674471921349 4865976372756313963485253)
                  ·
                    refine ⟨912370569891808868153485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4865976372756313963485253 912370569891808868153485)
                    ·
                      rfl

theorem cell23_5330506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_5330506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330506 prefixEnd_5330506 := by exact prefixLift 5330506
  have htrace : WordTrace (prefixWord ++ tailWord_5330506) baseStart_5330506 baseEnd_5330506 := by
    simpa [prefixWord, tailWord_5330506, baseEnd_5330506] using wordTrace_append hprefix tailTrace_5330506
  have hstable : (prefixWord ++ tailWord_5330506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330506).length < 2 ^ (prefixWord ++ tailWord_5330506).sum := by decide
  have hdescent : baseEnd_5330506 < baseStart_5330506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330516 : List Nat := [2, 4, 1, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_5330516 : Nat := 118140960795 + 5330516 * 2 ^ 59
def prefixEnd_5330516 : Nat := 4983230072969 + 3 ^ 40 * 5330516 * 2
def baseEnd_5330516 : Nat := 2737116844481971565335409

theorem tailTrace_5330516 : CollatzResearch.WordTrace tailWord_5330516 prefixEnd_5330516 2737116844481971565335409 := by
  unfold tailWord_5330516
  simp only [CollatzResearch.WordTrace]
  refine ⟨97209945378229193249441701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129613260504305590999255601 97209945378229193249441701)
  ·
    refine ⟨18226864758417973734270319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97209945378229193249441701 18226864758417973734270319)
    ·
      refine ⟨27340297137626960601405479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18226864758417973734270319 27340297137626960601405479)
      ·
        refine ⟨41010445706440440902108219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27340297137626960601405479 41010445706440440902108219)
        ·
          refine ⟨61515668559660661353162329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41010445706440440902108219 61515668559660661353162329)
          ·
            refine ⟨46136751419745496014871747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61515668559660661353162329 46136751419745496014871747)
            ·
              refine ⟨69205127129618244022307621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46136751419745496014871747 69205127129618244022307621)
              ·
                refine ⟨12975961336803420754182679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69205127129618244022307621 12975961336803420754182679)
                ·
                  refine ⟨19463942005205131131274019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12975961336803420754182679 19463942005205131131274019)
                  ·
                    refine ⟨29195913007807696696911029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19463942005205131131274019 29195913007807696696911029)
                    ·
                      refine ⟨2737116844481971565335409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29195913007807696696911029 2737116844481971565335409)
                      ·
                        rfl

theorem cell23_5330516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_5330516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330516 prefixEnd_5330516 := by exact prefixLift 5330516
  have htrace : WordTrace (prefixWord ++ tailWord_5330516) baseStart_5330516 baseEnd_5330516 := by
    simpa [prefixWord, tailWord_5330516, baseEnd_5330516] using wordTrace_append hprefix tailTrace_5330516
  have hstable : (prefixWord ++ tailWord_5330516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330516).length < 2 ^ (prefixWord ++ tailWord_5330516).sum := by decide
  have hdescent : baseEnd_5330516 < baseStart_5330516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330519 : List Nat := [1, 1, 3, 2, 2, 3, 1, 10]
def baseStart_5330519 : Nat := 118140960795 + 5330519 * 2 ^ 59
def prefixEnd_5330519 : Nat := 4983230072969 + 3 ^ 40 * 5330519 * 2
def baseEnd_5330519 : Nat := 101374754997182779762885

theorem tailTrace_5330519 : CollatzResearch.WordTrace tailWord_5330519 prefixEnd_5330519 101374754997182779762885 := by
  unfold tailWord_5330519
  simp only [CollatzResearch.WordTrace]
  refine ⟨194420000175447518011242611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129613333450298345340828407 194420000175447518011242611)
  ·
    refine ⟨291630000263171277016863917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194420000175447518011242611 291630000263171277016863917)
    ·
      refine ⟨109361250098689228881323969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291630000263171277016863917 109361250098689228881323969)
      ·
        refine ⟨82020937574016921660992977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109361250098689228881323969 82020937574016921660992977)
        ·
          refine ⟨61515703180512691245744733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82020937574016921660992977 61515703180512691245744733)
          ·
            refine ⟨23068388692692259217154275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61515703180512691245744733 23068388692692259217154275)
            ·
              refine ⟨34602583039038388825731413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23068388692692259217154275 34602583039038388825731413)
              ·
                refine ⟨101374754997182779762885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34602583039038388825731413 101374754997182779762885)
                ·
                  rfl

theorem cell23_5330519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 10].length) (baseStart_5330519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330519 prefixEnd_5330519 := by exact prefixLift 5330519
  have htrace : WordTrace (prefixWord ++ tailWord_5330519) baseStart_5330519 baseEnd_5330519 := by
    simpa [prefixWord, tailWord_5330519, baseEnd_5330519] using wordTrace_append hprefix tailTrace_5330519
  have hstable : (prefixWord ++ tailWord_5330519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330519).length < 2 ^ (prefixWord ++ tailWord_5330519).sum := by decide
  have hdescent : baseEnd_5330519 < baseStart_5330519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330533 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 3, 2, 3]
def baseStart_5330533 : Nat := 118140960795 + 5330533 * 2 ^ 59
def prefixEnd_5330533 : Nat := 4983230072969 + 3 ^ 40 * 5330533 * 2
def baseEnd_5330533 : Nat := 2737125573653097998822831

theorem tailTrace_5330533 : CollatzResearch.WordTrace tailWord_5330533 prefixEnd_5330533 2737125573653097998822831 := by
  unfold tailWord_5330533
  simp only [CollatzResearch.WordTrace]
  refine ⟨194420510797396798402252253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129613673864931198934834835 194420510797396798402252253)
  ·
    refine ⟨72907691549023799400844595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194420510797396798402252253 72907691549023799400844595)
    ·
      refine ⟨109361537323535699101266893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72907691549023799400844595 109361537323535699101266893)
      ·
        refine ⟨41010576496325887162975085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109361537323535699101266893 41010576496325887162975085)
        ·
          refine ⟨15378966186122207686115657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41010576496325887162975085 15378966186122207686115657)
          ·
            refine ⟨11534224639591655764586743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15378966186122207686115657 11534224639591655764586743)
            ·
              refine ⟨17301336959387483646880115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11534224639591655764586743 17301336959387483646880115)
              ·
                refine ⟨25952005439081225470320173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17301336959387483646880115 25952005439081225470320173)
                ·
                  refine ⟨9732002039655459551370065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25952005439081225470320173 9732002039655459551370065)
                  ·
                    refine ⟨7299001529741594663527549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9732002039655459551370065 7299001529741594663527549)
                    ·
                      refine ⟨2737125573653097998822831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7299001529741594663527549 2737125573653097998822831)
                      ·
                        rfl

theorem cell23_5330533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_5330533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330533 prefixEnd_5330533 := by exact prefixLift 5330533
  have htrace : WordTrace (prefixWord ++ tailWord_5330533) baseStart_5330533 baseEnd_5330533 := by
    simpa [prefixWord, tailWord_5330533, baseEnd_5330533] using wordTrace_append hprefix tailTrace_5330533
  have hstable : (prefixWord ++ tailWord_5330533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330533).length < 2 ^ (prefixWord ++ tailWord_5330533).sum := by decide
  have hdescent : baseEnd_5330533 < baseStart_5330533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330536 : List Nat := [2, 1, 4, 3, 1, 1, 2, 9]
def baseStart_5330536 : Nat := 118140960795 + 5330536 * 2 ^ 59
def prefixEnd_5330536 : Nat := 4983230072969 + 3 ^ 40 * 5330536 * 2
def baseEnd_5330536 : Nat := 101375078299817092114271

theorem tailTrace_5330536 : CollatzResearch.WordTrace tailWord_5330536 prefixEnd_5330536 101375078299817092114271 := by
  unfold tailWord_5330536
  simp only [CollatzResearch.WordTrace]
  refine ⟨97210310108192964957305731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129613746810923953276407641 97210310108192964957305731)
  ·
    refine ⟨145815465162289447435958597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97210310108192964957305731 145815465162289447435958597)
    ·
      refine ⟨27340399717929271394242237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145815465162289447435958597 27340399717929271394242237)
      ·
        refine ⟨10252649894223476772840839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27340399717929271394242237 10252649894223476772840839)
        ·
          refine ⟨15378974841335215159261259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10252649894223476772840839 15378974841335215159261259)
          ·
            refine ⟨23068462262002822738891889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15378974841335215159261259 23068462262002822738891889)
            ·
              refine ⟨17301346696502117054168917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23068462262002822738891889 17301346696502117054168917)
              ·
                refine ⟨101375078299817092114271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17301346696502117054168917 101375078299817092114271)
                ·
                  rfl

theorem cell23_5330536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 9].length) (baseStart_5330536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330536 prefixEnd_5330536 := by exact prefixLift 5330536
  have htrace : WordTrace (prefixWord ++ tailWord_5330536) baseStart_5330536 baseEnd_5330536 := by
    simpa [prefixWord, tailWord_5330536, baseEnd_5330536] using wordTrace_append hprefix tailTrace_5330536
  have hstable : (prefixWord ++ tailWord_5330536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330536).length < 2 ^ (prefixWord ++ tailWord_5330536).sum := by decide
  have hdescent : baseEnd_5330536 < baseStart_5330536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330550 : List Nat := [5, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_5330550 : Nat := 118140960795 + 5330550 * 2 ^ 59
def prefixEnd_5330550 : Nat := 4983230072969 + 3 ^ 40 * 5330550 * 2
def baseEnd_5330550 : Nat := 2737134302824224432310253

theorem tailTrace_5330550 : CollatzResearch.WordTrace tailWord_5330550 prefixEnd_5330550 2737134302824224432310253 := by
  unfold tailWord_5330550
  simp only [CollatzResearch.WordTrace]
  refine ⟨12151320677395950644101319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129614087225556806870414069 12151320677395950644101319)
  ·
    refine ⟨18226981016093925966151979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12151320677395950644101319 18226981016093925966151979)
    ·
      refine ⟨27340471524140888949227969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18226981016093925966151979 27340471524140888949227969)
      ·
        refine ⟨20505353643105666711920977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27340471524140888949227969 20505353643105666711920977)
        ·
          refine ⟨15379015232329250033940733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20505353643105666711920977 15379015232329250033940733)
          ·
            refine ⟨5767130712123468762727775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15379015232329250033940733 5767130712123468762727775)
            ·
              refine ⟨8650696068185203144091663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5767130712123468762727775 8650696068185203144091663)
              ·
                refine ⟨12976044102277804716137495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8650696068185203144091663 12976044102277804716137495)
                ·
                  refine ⟨19464066153416707074206243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12976044102277804716137495 19464066153416707074206243)
                  ·
                    refine ⟨29196099230125060611309365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19464066153416707074206243 29196099230125060611309365)
                    ·
                      refine ⟨2737134302824224432310253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29196099230125060611309365 2737134302824224432310253)
                      ·
                        rfl

theorem cell23_5330550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_5330550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330550 prefixEnd_5330550 := by exact prefixLift 5330550
  have htrace : WordTrace (prefixWord ++ tailWord_5330550) baseStart_5330550 baseEnd_5330550 := by
    simpa [prefixWord, tailWord_5330550, baseEnd_5330550] using wordTrace_append hprefix tailTrace_5330550
  have hstable : (prefixWord ++ tailWord_5330550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330550).length < 2 ^ (prefixWord ++ tailWord_5330550).sum := by decide
  have hdescent : baseEnd_5330550 < baseStart_5330550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330559 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 5]
def baseStart_5330559 : Nat := 118140960795 + 5330559 * 2 ^ 59
def prefixEnd_5330559 : Nat := 4983230072969 + 3 ^ 40 * 5330559 * 2
def baseEnd_5330559 : Nat := 2737138924150114897097711

theorem tailTrace_5330559 : CollatzResearch.WordTrace tailWord_5330559 prefixEnd_5330559 2737138924150114897097711 := by
  unfold tailWord_5330559
  simp only [CollatzResearch.WordTrace]
  refine ⟨194421459095302604842698731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129614306063535069895132487 194421459095302604842698731)
  ·
    refine ⟨291632188642953907264048097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194421459095302604842698731 291632188642953907264048097)
    ·
      refine ⟨218724141482215430448036073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291632188642953907264048097 218724141482215430448036073)
      ·
        refine ⟨164043106111661572836027055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218724141482215430448036073 164043106111661572836027055)
        ·
          refine ⟨246064659167492359254040583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164043106111661572836027055 246064659167492359254040583)
          ·
            refine ⟨369096988751238538881060875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246064659167492359254040583 369096988751238538881060875)
            ·
              refine ⟨553645483126857808321591313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369096988751238538881060875 553645483126857808321591313)
              ·
                refine ⟨415234112345143356241193485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553645483126857808321591313 415234112345143356241193485)
                ·
                  refine ⟨155712792129428758590447557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 415234112345143356241193485 155712792129428758590447557)
                  ·
                    refine ⟨29196148524267892235708917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 155712792129428758590447557 29196148524267892235708917)
                    ·
                      refine ⟨2737138924150114897097711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29196148524267892235708917 2737138924150114897097711)
                      ·
                        rfl

theorem cell23_5330559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_5330559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330559 prefixEnd_5330559 := by exact prefixLift 5330559
  have htrace : WordTrace (prefixWord ++ tailWord_5330559) baseStart_5330559 baseEnd_5330559 := by
    simpa [prefixWord, tailWord_5330559, baseEnd_5330559] using wordTrace_append hprefix tailTrace_5330559
  have hstable : (prefixWord ++ tailWord_5330559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330559).length < 2 ^ (prefixWord ++ tailWord_5330559).sum := by decide
  have hdescent : baseEnd_5330559 < baseStart_5330559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330564 : List Nat := [2, 3, 2, 1, 4, 1, 1, 4, 1, 2, 2]
def baseStart_5330564 : Nat := 118140960795 + 5330564 * 2 ^ 59
def prefixEnd_5330564 : Nat := 4983230072969 + 3 ^ 40 * 5330564 * 2
def baseEnd_5330564 : Nat := 2737141491553387377535189

theorem tailTrace_5330564 : CollatzResearch.WordTrace tailWord_5330564 prefixEnd_5330564 2737141491553387377535189 := by
  unfold tailWord_5330564
  simp only [CollatzResearch.WordTrace]
  refine ⟨97210820730142245348315373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129614427640189660464420497 97210820730142245348315373)
  ·
    refine ⟨36454057773803342005618265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97210820730142245348315373 36454057773803342005618265)
    ·
      refine ⟨27340543330352506504213699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36454057773803342005618265 27340543330352506504213699)
      ·
        refine ⟨41010814995528759756320549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27340543330352506504213699 41010814995528759756320549)
        ·
          refine ⟨7689527811661642454310103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41010814995528759756320549 7689527811661642454310103)
          ·
            refine ⟨11534291717492463681465155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7689527811661642454310103 11534291717492463681465155)
            ·
              refine ⟨17301437576238695522197733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11534291717492463681465155 17301437576238695522197733)
              ·
                refine ⟨3244019545544755410412075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17301437576238695522197733 3244019545544755410412075)
                ·
                  refine ⟨4866029318317133115618113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3244019545544755410412075 4866029318317133115618113)
                  ·
                    refine ⟨3649521988737849836713585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4866029318317133115618113 3649521988737849836713585)
                    ·
                      refine ⟨2737141491553387377535189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3649521988737849836713585 2737141491553387377535189)
                      ·
                        rfl

theorem cell23_5330564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_5330564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330564 prefixEnd_5330564 := by exact prefixLift 5330564
  have htrace : WordTrace (prefixWord ++ tailWord_5330564) baseStart_5330564 baseEnd_5330564 := by
    simpa [prefixWord, tailWord_5330564, baseEnd_5330564] using wordTrace_append hprefix tailTrace_5330564
  have hstable : (prefixWord ++ tailWord_5330564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330564).length < 2 ^ (prefixWord ++ tailWord_5330564).sum := by decide
  have hdescent : baseEnd_5330564 < baseStart_5330564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330614 : List Nat := [5, 1, 3, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_5330614 : Nat := 118140960795 + 5330614 * 2 ^ 59
def prefixEnd_5330614 : Nat := 4983230072969 + 3 ^ 40 * 5330614 * 2
def baseEnd_5330614 : Nat := 2737167165586112181909959

theorem tailTrace_5330614 : CollatzResearch.WordTrace tailWord_5330614 prefixEnd_5330614 2737167165586112181909959 := by
  unfold tailWord_5330614
  simp only [CollatzResearch.WordTrace]
  refine ⟨12151466569381459327246931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129615643406735566157300597 12151466569381459327246931)
  ·
    refine ⟨18227199854072188990870397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12151466569381459327246931 18227199854072188990870397)
    ·
      refine ⟨6835199945277070871576399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18227199854072188990870397 6835199945277070871576399)
      ·
        refine ⟨10252799917915606307364599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6835199945277070871576399 10252799917915606307364599)
        ·
          refine ⟨15379199876873409461046899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10252799917915606307364599 15379199876873409461046899)
          ·
            refine ⟨23068799815310114191570349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15379199876873409461046899 23068799815310114191570349)
            ·
              refine ⟨8650799930741292821838881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23068799815310114191570349 8650799930741292821838881)
              ·
                refine ⟨6488099948055969616379161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8650799930741292821838881 6488099948055969616379161)
                ·
                  refine ⟨4866074961041977212284371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6488099948055969616379161 4866074961041977212284371)
                  ·
                    refine ⟨7299112441562965818426557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4866074961041977212284371 7299112441562965818426557)
                    ·
                      refine ⟨2737167165586112181909959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7299112441562965818426557 2737167165586112181909959)
                      ·
                        rfl

theorem cell23_5330614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_5330614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330614 prefixEnd_5330614 := by exact prefixLift 5330614
  have htrace : WordTrace (prefixWord ++ tailWord_5330614) baseStart_5330614 baseEnd_5330614 := by
    simpa [prefixWord, tailWord_5330614, baseEnd_5330614] using wordTrace_append hprefix tailTrace_5330614
  have hstable : (prefixWord ++ tailWord_5330614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330614).length < 2 ^ (prefixWord ++ tailWord_5330614).sum := by decide
  have hdescent : baseEnd_5330614 < baseStart_5330614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330656 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 1, 7]
def baseStart_5330656 : Nat := 118140960795 + 5330656 * 2 ^ 59
def prefixEnd_5330656 : Nat := 4983230072969 + 3 ^ 40 * 5330656 * 2
def baseEnd_5330656 : Nat := 912396243924533672528255

theorem tailTrace_5330656 : CollatzResearch.WordTrace tailWord_5330656 prefixEnd_5330656 912396243924533672528255 := by
  unfold tailWord_5330656
  simp only [CollatzResearch.WordTrace]
  refine ⟨97212498487975595204489911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129616664650634126939319881 97212498487975595204489911)
  ·
    refine ⟨145818747731963392806734867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97212498487975595204489911 145818747731963392806734867)
    ·
      refine ⟨218728121597945089210102301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145818747731963392806734867 218728121597945089210102301)
      ·
        refine ⟨82023045599229408453788363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218728121597945089210102301 82023045599229408453788363)
        ·
          refine ⟨123034568398844112680682545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82023045599229408453788363 123034568398844112680682545)
          ·
            refine ⟨92275926299133084510511909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123034568398844112680682545 92275926299133084510511909)
            ·
              refine ⟨17301736181087453345720983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92275926299133084510511909 17301736181087453345720983)
              ·
                refine ⟨25952604271631180018581475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17301736181087453345720983 25952604271631180018581475)
                ·
                  refine ⟨38928906407446770027872213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25952604271631180018581475 38928906407446770027872213)
                  ·
                    refine ⟨912396243924533672528255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38928906407446770027872213 912396243924533672528255)
                    ·
                      rfl

theorem cell23_5330656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 1, 7].length) (baseStart_5330656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330656 prefixEnd_5330656 := by exact prefixLift 5330656
  have htrace : WordTrace (prefixWord ++ tailWord_5330656) baseStart_5330656 baseEnd_5330656 := by
    simpa [prefixWord, tailWord_5330656, baseEnd_5330656] using wordTrace_append hprefix tailTrace_5330656
  have hstable : (prefixWord ++ tailWord_5330656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330656).length < 2 ^ (prefixWord ++ tailWord_5330656).sum := by decide
  have hdescent : baseEnd_5330656 < baseStart_5330656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330673 : List Nat := [1, 2, 2, 2, 2, 4, 1, 2, 2, 5]
def baseStart_5330673 : Nat := 118140960795 + 5330673 * 2 ^ 59
def prefixEnd_5330673 : Nat := 4983230072969 + 3 ^ 40 * 5330673 * 2
def baseEnd_5330673 : Nat := 912399153648242483690729

theorem tailTrace_5330673 : CollatzResearch.WordTrace tailWord_5330673 prefixEnd_5330673 912399153648242483690729 := by
  unfold tailWord_5330673
  simp only [CollatzResearch.WordTrace]
  refine ⟨194425617016889602312348673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129617078011259734874899115 194425617016889602312348673)
  ·
    refine ⟨145819212762667201734261505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194425617016889602312348673 145819212762667201734261505)
    ·
      refine ⟨109364409572000401300696129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145819212762667201734261505 109364409572000401300696129)
      ·
        refine ⟨82023307179000300975522097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109364409572000401300696129 82023307179000300975522097)
        ·
          refine ⟨61517480384250225731641573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82023307179000300975522097 61517480384250225731641573)
          ·
            refine ⟨11534527572046917324682795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61517480384250225731641573 11534527572046917324682795)
            ·
              refine ⟨17301791358070375987024193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11534527572046917324682795 17301791358070375987024193)
              ·
                refine ⟨12976343518552781990268145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17301791358070375987024193 12976343518552781990268145)
                ·
                  refine ⟨9732257638914586492701109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12976343518552781990268145 9732257638914586492701109)
                  ·
                    refine ⟨912399153648242483690729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9732257638914586492701109 912399153648242483690729)
                    ·
                      rfl

theorem cell23_5330673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_5330673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330673 prefixEnd_5330673 := by exact prefixLift 5330673
  have htrace : WordTrace (prefixWord ++ tailWord_5330673) baseStart_5330673 baseEnd_5330673 := by
    simpa [prefixWord, tailWord_5330673, baseEnd_5330673] using wordTrace_append hprefix tailTrace_5330673
  have hstable : (prefixWord ++ tailWord_5330673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330673).length < 2 ^ (prefixWord ++ tailWord_5330673).sum := by decide
  have hdescent : baseEnd_5330673 < baseStart_5330673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330737 : List Nat := [1, 2, 2, 3, 2, 3, 1, 4, 1, 4]
def baseStart_5330737 : Nat := 118140960795 + 5330737 * 2 ^ 59
def prefixEnd_5330737 : Nat := 4983230072969 + 3 ^ 40 * 5330737 * 2
def baseEnd_5330737 : Nat := 912410107902205066890631

theorem tailTrace_5330737 : CollatzResearch.WordTrace tailWord_5330737 prefixEnd_5330737 912410107902205066890631 := by
  unfold tailWord_5330737
  simp only [CollatzResearch.WordTrace]
  refine ⟨194427951288657741242678465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129618634192438494161785643 194427951288657741242678465)
  ·
    refine ⟨145820963466493305932008849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194427951288657741242678465 145820963466493305932008849)
    ·
      refine ⟨109365722599869979449006637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145820963466493305932008849 109365722599869979449006637)
      ·
        refine ⟨41012145974951242293377489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109365722599869979449006637 41012145974951242293377489)
        ·
          refine ⟨30759109481213431720033117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41012145974951242293377489 30759109481213431720033117)
          ·
            refine ⟨11534666055455036895012419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30759109481213431720033117 11534666055455036895012419)
            ·
              refine ⟨17301999083182555342518629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11534666055455036895012419 17301999083182555342518629)
              ·
                refine ⟨3244124828096729126722243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17301999083182555342518629 3244124828096729126722243)
                ·
                  refine ⟨4866187242145093690083365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3244124828096729126722243 4866187242145093690083365)
                  ·
                    refine ⟨912410107902205066890631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4866187242145093690083365 912410107902205066890631)
                    ·
                      rfl

theorem cell23_5330737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 1, 4].length) (baseStart_5330737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330737 prefixEnd_5330737 := by exact prefixLift 5330737
  have htrace : WordTrace (prefixWord ++ tailWord_5330737) baseStart_5330737 baseEnd_5330737 := by
    simpa [prefixWord, tailWord_5330737, baseEnd_5330737] using wordTrace_append hprefix tailTrace_5330737
  have hstable : (prefixWord ++ tailWord_5330737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330737).length < 2 ^ (prefixWord ++ tailWord_5330737).sum := by decide
  have hdescent : baseEnd_5330737 < baseStart_5330737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330750 : List Nat := [4, 2, 1, 2, 2, 1, 2, 3, 6]
def baseStart_5330750 : Nat := 118140960795 + 5330750 * 2 ^ 59
def prefixEnd_5330750 : Nat := 4983230072969 + 3 ^ 40 * 5330750 * 2
def baseEnd_5330750 : Nat := 304137444328347072201037

theorem tailTrace_5330750 : CollatzResearch.WordTrace tailWord_5330750 prefixEnd_5330750 304137444328347072201037 := by
  unfold tailWord_5330750
  simp only [CollatzResearch.WordTrace]
  refine ⟨24303553179701330557862713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129618950291740429641934469 24303553179701330557862713)
  ·
    refine ⟨18227664884775997918397035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24303553179701330557862713 18227664884775997918397035)
    ·
      refine ⟨27341497327163996877595553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18227664884775997918397035 27341497327163996877595553)
      ·
        refine ⟨20506122995372997658196665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27341497327163996877595553 20506122995372997658196665)
        ·
          refine ⟨15379592246529748243647499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20506122995372997658196665 15379592246529748243647499)
          ·
            refine ⟨23069388369794622365471249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15379592246529748243647499 23069388369794622365471249)
            ·
              refine ⟨17302041277345966774103437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23069388369794622365471249 17302041277345966774103437)
              ·
                refine ⟨6488265479004737540288789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17302041277345966774103437 6488265479004737540288789)
                ·
                  refine ⟨304137444328347072201037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6488265479004737540288789 304137444328347072201037)
                  ·
                    rfl

theorem cell23_5330750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_5330750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330750 prefixEnd_5330750 := by exact prefixLift 5330750
  have htrace : WordTrace (prefixWord ++ tailWord_5330750) baseStart_5330750 baseEnd_5330750 := by
    simpa [prefixWord, tailWord_5330750, baseEnd_5330750] using wordTrace_append hprefix tailTrace_5330750
  have hstable : (prefixWord ++ tailWord_5330750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330750).length < 2 ^ (prefixWord ++ tailWord_5330750).sum := by decide
  have hdescent : baseEnd_5330750 < baseStart_5330750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330760 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 5, 1, 3]
def baseStart_5330760 : Nat := 118140960795 + 5330760 * 2 ^ 59
def prefixEnd_5330760 : Nat := 4983230072969 + 3 ^ 40 * 5330760 * 2
def baseEnd_5330760 : Nat := 2737242133761668610684287

theorem tailTrace_5330760 : CollatzResearch.WordTrace tailWord_5330760 prefixEnd_5330760 2737242133761668610684287 := by
  unfold tailWord_5330760
  simp only [CollatzResearch.WordTrace]
  refine ⟨97214395083787208085382867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129619193445049610780510489 97214395083787208085382867)
  ·
    refine ⟨145821592625680812128074301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97214395083787208085382867 145821592625680812128074301)
    ·
      refine ⟨54683097234630304548027863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145821592625680812128074301 54683097234630304548027863)
      ·
        refine ⟨82024645851945456822041795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54683097234630304548027863 82024645851945456822041795)
        ·
          refine ⟨123036968777918185233062693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82024645851945456822041795 123036968777918185233062693)
          ·
            refine ⟨23069431645859659731199255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123036968777918185233062693 23069431645859659731199255)
            ·
              refine ⟨34604147468789489596798883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23069431645859659731199255 34604147468789489596798883)
              ·
                refine ⟨51906221203184234395198325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34604147468789489596798883 51906221203184234395198325)
                ·
                  refine ⟨4866208237798521974549843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51906221203184234395198325 4866208237798521974549843)
                  ·
                    refine ⟨7299312356697782961824765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4866208237798521974549843 7299312356697782961824765)
                    ·
                      refine ⟨2737242133761668610684287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7299312356697782961824765 2737242133761668610684287)
                      ·
                        rfl

theorem cell23_5330760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_5330760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330760 prefixEnd_5330760 := by exact prefixLift 5330760
  have htrace : WordTrace (prefixWord ++ tailWord_5330760) baseStart_5330760 baseEnd_5330760 := by
    simpa [prefixWord, tailWord_5330760, baseEnd_5330760] using wordTrace_append hprefix tailTrace_5330760
  have hstable : (prefixWord ++ tailWord_5330760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330760).length < 2 ^ (prefixWord ++ tailWord_5330760).sum := by decide
  have hdescent : baseEnd_5330760 < baseStart_5330760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330764 : List Nat := [2, 2, 1, 3, 5, 1, 1, 1, 2, 2, 3]
def baseStart_5330764 : Nat := 118140960795 + 5330764 * 2 ^ 59
def prefixEnd_5330764 : Nat := 4983230072969 + 3 ^ 40 * 5330764 * 2
def baseEnd_5330764 : Nat := 2737244187684286595034269

theorem tailTrace_5330764 : CollatzResearch.WordTrace tailWord_5330764 prefixEnd_5330764 2737244187684286595034269 := by
  unfold tailWord_5330764
  simp only [CollatzResearch.WordTrace]
  refine ⟨97214468029779962426955673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129619290706373283235940897 97214468029779962426955673)
  ·
    refine ⟨72910851022334971820216755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97214468029779962426955673 72910851022334971820216755)
    ·
      refine ⟨109366276533502457730325133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72910851022334971820216755 109366276533502457730325133)
      ·
        refine ⟨41012353700063421648871925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109366276533502457730325133 41012353700063421648871925)
        ·
          refine ⟨3844908159380945779581743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41012353700063421648871925 3844908159380945779581743)
          ·
            refine ⟨5767362239071418669372615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3844908159380945779581743 5767362239071418669372615)
            ·
              refine ⟨8651043358607128004058923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5767362239071418669372615 8651043358607128004058923)
              ·
                refine ⟨12976565037910692006088385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8651043358607128004058923 12976565037910692006088385)
                ·
                  refine ⟨9732423778433019004566289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12976565037910692006088385 9732423778433019004566289)
                  ·
                    refine ⟨7299317833824764253424717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9732423778433019004566289 7299317833824764253424717)
                    ·
                      refine ⟨2737244187684286595034269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7299317833824764253424717 2737244187684286595034269)
                      ·
                        rfl

theorem cell23_5330764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_5330764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330764 prefixEnd_5330764 := by exact prefixLift 5330764
  have htrace : WordTrace (prefixWord ++ tailWord_5330764) baseStart_5330764 baseEnd_5330764 := by
    simpa [prefixWord, tailWord_5330764, baseEnd_5330764] using wordTrace_append hprefix tailTrace_5330764
  have hstable : (prefixWord ++ tailWord_5330764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330764).length < 2 ^ (prefixWord ++ tailWord_5330764).sum := by decide
  have hdescent : baseEnd_5330764 < baseStart_5330764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330810 : List Nat := [3, 1, 1, 1, 1, 1, 4, 5, 2, 4]
def baseStart_5330810 : Nat := 118140960795 + 5330810 * 2 ^ 59
def prefixEnd_5330810 : Nat := 4983230072969 + 3 ^ 40 * 5330810 * 2
def baseEnd_5330810 : Nat := 912422602598131138353019

theorem tailTrace_5330810 : CollatzResearch.WordTrace tailWord_5330810 prefixEnd_5330810 912422602598131138353019 := by
  unfold tailWord_5330810
  simp only [CollatzResearch.WordTrace]
  refine ⟨48607653454348318677521471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129620409211595516473390589 48607653454348318677521471)
  ·
    refine ⟨72911480181522478016282207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48607653454348318677521471 72911480181522478016282207)
    ·
      refine ⟨109367220272283717024423311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72911480181522478016282207 109367220272283717024423311)
      ·
        refine ⟨164050830408425575536634967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109367220272283717024423311 164050830408425575536634967)
        ·
          refine ⟨246076245612638363304952451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164050830408425575536634967 246076245612638363304952451)
          ·
            refine ⟨369114368418957544957428677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246076245612638363304952451 369114368418957544957428677)
            ·
              refine ⟨69208944078554539679517877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 369114368418957544957428677 69208944078554539679517877)
              ·
                refine ⟨6488338507364488094954801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69208944078554539679517877 6488338507364488094954801)
                ·
                  refine ⟨4866253880523366071216101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6488338507364488094954801 4866253880523366071216101)
                  ·
                    refine ⟨912422602598131138353019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4866253880523366071216101 912422602598131138353019)
                    ·
                      rfl

theorem cell23_5330810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_5330810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330810 prefixEnd_5330810 := by exact prefixLift 5330810
  have htrace : WordTrace (prefixWord ++ tailWord_5330810) baseStart_5330810 baseEnd_5330810 := by
    simpa [prefixWord, tailWord_5330810, baseEnd_5330810] using wordTrace_append hprefix tailTrace_5330810
  have hstable : (prefixWord ++ tailWord_5330810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330810).length < 2 ^ (prefixWord ++ tailWord_5330810).sum := by decide
  have hdescent : baseEnd_5330810 < baseStart_5330810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330814 : List Nat := [4, 2, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_5330814 : Nat := 118140960795 + 5330814 * 2 ^ 59
def prefixEnd_5330814 : Nat := 4983230072969 + 3 ^ 40 * 5330814 * 2
def baseEnd_5330814 : Nat := 912423287239003799803013

theorem tailTrace_5330814 : CollatzResearch.WordTrace tailWord_5330814 prefixEnd_5330814 912423287239003799803013 := by
  unfold tailWord_5330814
  simp only [CollatzResearch.WordTrace]
  refine ⟨24303844963672347924153937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129620506472919188928820997 24303844963672347924153937)
  ·
    refine ⟨18227883722754260943115453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24303844963672347924153937 18227883722754260943115453)
    ·
      refine ⟨6835456396032847853668295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18227883722754260943115453 6835456396032847853668295)
      ·
        refine ⟨10253184594049271780502443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6835456396032847853668295 10253184594049271780502443)
        ·
          refine ⟨15379776891073907670753665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10253184594049271780502443 15379776891073907670753665)
          ·
            refine ⟨11534832668305430753065249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15379776891073907670753665 11534832668305430753065249)
            ·
              refine ⟨8651124501229073064798937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11534832668305430753065249 8651124501229073064798937)
              ·
                refine ⟨6488343375921804798599203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8651124501229073064798937 6488343375921804798599203)
                ·
                  refine ⟨9732515063882707197898805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6488343375921804798599203 9732515063882707197898805)
                  ·
                    refine ⟨912423287239003799803013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9732515063882707197898805 912423287239003799803013)
                    ·
                      rfl

theorem cell23_5330814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_5330814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330814 prefixEnd_5330814 := by exact prefixLift 5330814
  have htrace : WordTrace (prefixWord ++ tailWord_5330814) baseStart_5330814 baseEnd_5330814 := by
    simpa [prefixWord, tailWord_5330814, baseEnd_5330814] using wordTrace_append hprefix tailTrace_5330814
  have hstable : (prefixWord ++ tailWord_5330814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330814).length < 2 ^ (prefixWord ++ tailWord_5330814).sum := by decide
  have hdescent : baseEnd_5330814 < baseStart_5330814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330820 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_5330820 : Nat := 118140960795 + 5330820 * 2 ^ 59
def prefixEnd_5330820 : Nat := 4983230072969 + 3 ^ 40 * 5330820 * 2
def baseEnd_5330820 : Nat := 2737272942600938375934011

theorem tailTrace_5330820 : CollatzResearch.WordTrace tailWord_5330820 prefixEnd_5330820 2737272942600938375934011 := by
  unfold tailWord_5330820
  simp only [CollatzResearch.WordTrace]
  refine ⟨97215489273678523208974957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129620652364904697611966609 97215489273678523208974957)
  ·
    refine ⟨36455808477629446203365609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97215489273678523208974957 36455808477629446203365609)
    ·
      refine ⟨27341856358222084652524207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36455808477629446203365609 27341856358222084652524207)
      ·
        refine ⟨41012784537333126978786311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27341856358222084652524207 41012784537333126978786311)
        ·
          refine ⟨61519176805999690468179467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41012784537333126978786311 61519176805999690468179467)
          ·
            refine ⟨92278765208999535702269201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61519176805999690468179467 92278765208999535702269201)
            ·
              refine ⟨69209073906749651776701901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92278765208999535702269201 69209073906749651776701901)
              ·
                refine ⟨25953402715031119416263213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69209073906749651776701901 25953402715031119416263213)
                ·
                  refine ⟨9732526018136669781098705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25953402715031119416263213 9732526018136669781098705)
                  ·
                    refine ⟨7299394513602502335824029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9732526018136669781098705 7299394513602502335824029)
                    ·
                      refine ⟨2737272942600938375934011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7299394513602502335824029 2737272942600938375934011)
                      ·
                        rfl

theorem cell23_5330820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_5330820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330820 prefixEnd_5330820 := by exact prefixLift 5330820
  have htrace : WordTrace (prefixWord ++ tailWord_5330820) baseStart_5330820 baseEnd_5330820 := by
    simpa [prefixWord, tailWord_5330820, baseEnd_5330820] using wordTrace_append hprefix tailTrace_5330820
  have hstable : (prefixWord ++ tailWord_5330820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330820).length < 2 ^ (prefixWord ++ tailWord_5330820).sum := by decide
  have hdescent : baseEnd_5330820 < baseStart_5330820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330838 : List Nat := [5, 3, 1, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_5330838 : Nat := 118140960795 + 5330838 * 2 ^ 59
def prefixEnd_5330838 : Nat := 4983230072969 + 3 ^ 40 * 5330838 * 2
def baseEnd_5330838 : Nat := 2737282185252719305508929

theorem tailTrace_5330838 : CollatzResearch.WordTrace tailWord_5330838 prefixEnd_5330838 2737282185252719305508929 := by
  unfold tailWord_5330838
  simp only [CollatzResearch.WordTrace]
  refine ⟨12151977191330739718256573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129621090040861223661403445 12151977191330739718256573)
  ·
    refine ⟨4556991446749027394346215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12151977191330739718256573 4556991446749027394346215)
    ·
      refine ⟨6835487170123541091519323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4556991446749027394346215 6835487170123541091519323)
      ·
        refine ⟨10253230755185311637278985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6835487170123541091519323 10253230755185311637278985)
        ·
          refine ⟨7689923066388983727959239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10253230755185311637278985 7689923066388983727959239)
          ·
            refine ⟨11534884599583475591938859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7689923066388983727959239 11534884599583475591938859)
            ·
              refine ⟨17302326899375213387908289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11534884599583475591938859 17302326899375213387908289)
              ·
                refine ⟨12976745174531410040931217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17302326899375213387908289 12976745174531410040931217)
                ·
                  refine ⟨9732558880898557530698413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12976745174531410040931217 9732558880898557530698413)
                  ·
                    refine ⟨3649709580336959074011905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9732558880898557530698413 3649709580336959074011905)
                    ·
                      refine ⟨2737282185252719305508929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3649709580336959074011905 2737282185252719305508929)
                      ·
                        rfl

theorem cell23_5330838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_5330838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330838 prefixEnd_5330838 := by exact prefixLift 5330838
  have htrace : WordTrace (prefixWord ++ tailWord_5330838) baseStart_5330838 baseEnd_5330838 := by
    simpa [prefixWord, tailWord_5330838, baseEnd_5330838] using wordTrace_append hprefix tailTrace_5330838
  have hstable : (prefixWord ++ tailWord_5330838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330838).length < 2 ^ (prefixWord ++ tailWord_5330838).sum := by decide
  have hdescent : baseEnd_5330838 < baseStart_5330838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330867 : List Nat := [1, 1, 1, 2, 3, 1, 5, 3, 2, 1, 3]
def baseStart_5330867 : Nat := 118140960795 + 5330867 * 2 ^ 59
def prefixEnd_5330867 : Nat := 4983230072969 + 3 ^ 40 * 5330867 * 2
def baseEnd_5330867 : Nat := 2737297076191699692046295

theorem tailTrace_5330867 : CollatzResearch.WordTrace tailWord_5330867 prefixEnd_5330867 2737297076191699692046295 := by
  unfold tailWord_5330867
  simp only [CollatzResearch.WordTrace]
  refine ⟨194432692778186773444910855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129621795185457848963273903 194432692778186773444910855)
  ·
    refine ⟨291649039167280160167366283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194432692778186773444910855 291649039167280160167366283)
    ·
      refine ⟨437473558750920240251049425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291649039167280160167366283 437473558750920240251049425)
      ·
        refine ⟨328105169063190180188287069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437473558750920240251049425 328105169063190180188287069)
        ·
          refine ⟨123039438398696317570607651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 328105169063190180188287069 123039438398696317570607651)
          ·
            refine ⟨184559157598044476355911477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123039438398696317570607651 184559157598044476355911477)
            ·
              refine ⟨17302421024816669658366701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184559157598044476355911477 17302421024816669658366701)
              ·
                refine ⟨6488407884306251121887513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17302421024816669658366701 6488407884306251121887513)
                ·
                  refine ⟨4866305913229688341415635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6488407884306251121887513 4866305913229688341415635)
                  ·
                    refine ⟨7299458869844532512123453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4866305913229688341415635 7299458869844532512123453)
                    ·
                      refine ⟨2737297076191699692046295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7299458869844532512123453 2737297076191699692046295)
                      ·
                        rfl

theorem cell23_5330867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 1, 3].length) (baseStart_5330867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330867 prefixEnd_5330867 := by exact prefixLift 5330867
  have htrace : WordTrace (prefixWord ++ tailWord_5330867) baseStart_5330867 baseEnd_5330867 := by
    simpa [prefixWord, tailWord_5330867, baseEnd_5330867] using wordTrace_append hprefix tailTrace_5330867
  have hstable : (prefixWord ++ tailWord_5330867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330867).length < 2 ^ (prefixWord ++ tailWord_5330867).sum := by decide
  have hdescent : baseEnd_5330867 < baseStart_5330867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330868 : List Nat := [2, 5, 2, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_5330868 : Nat := 118140960795 + 5330868 * 2 ^ 59
def prefixEnd_5330868 : Nat := 4983230072969 + 3 ^ 40 * 5330868 * 2
def baseEnd_5330868 : Nat := 2737297589672354188133791

theorem tailTrace_5330868 : CollatzResearch.WordTrace tailWord_5330868 prefixEnd_5330868 2737297589672354188133791 := by
  unfold tailWord_5330868
  simp only [CollatzResearch.WordTrace]
  refine ⟨97216364625591575307848629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129621819500788767077131505 97216364625591575307848629)
  ·
    refine ⟨9114034183649210185110809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97216364625591575307848629 9114034183649210185110809)
    ·
      refine ⟨6835525637736907638833107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9114034183649210185110809 6835525637736907638833107)
      ·
        refine ⟨10253288456605361458249661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6835525637736907638833107 10253288456605361458249661)
        ·
          refine ⟨3844983171227010546843623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10253288456605361458249661 3844983171227010546843623)
          ·
            refine ⟨5767474756840515820265435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3844983171227010546843623 5767474756840515820265435)
            ·
              refine ⟨8651212135260773730398153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5767474756840515820265435 8651212135260773730398153)
              ·
                refine ⟨6488409101445580297798615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8651212135260773730398153 6488409101445580297798615)
                ·
                  refine ⟨9732613652168370446697923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6488409101445580297798615 9732613652168370446697923)
                  ·
                    refine ⟨14598920478252555670046885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9732613652168370446697923 14598920478252555670046885)
                    ·
                      refine ⟨2737297589672354188133791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14598920478252555670046885 2737297589672354188133791)
                      ·
                        rfl

theorem cell23_5330868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_5330868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330868 prefixEnd_5330868 := by exact prefixLift 5330868
  have htrace : WordTrace (prefixWord ++ tailWord_5330868) baseStart_5330868 baseEnd_5330868 := by
    simpa [prefixWord, tailWord_5330868, baseEnd_5330868] using wordTrace_append hprefix tailTrace_5330868
  have hstable : (prefixWord ++ tailWord_5330868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330868).length < 2 ^ (prefixWord ++ tailWord_5330868).sum := by decide
  have hdescent : baseEnd_5330868 < baseStart_5330868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330900 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_5330900 : Nat := 118140960795 + 5330900 * 2 ^ 59
def prefixEnd_5330900 : Nat := 4983230072969 + 3 ^ 40 * 5330900 * 2
def baseEnd_5330900 : Nat := 912438007017766020977881

theorem tailTrace_5330900 : CollatzResearch.WordTrace tailWord_5330900 prefixEnd_5330900 912438007017766020977881 := by
  unfold tailWord_5330900
  simp only [CollatzResearch.WordTrace]
  refine ⟨97216948193533610040431077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129622597591378146720574769 97216948193533610040431077)
  ·
    refine ⟨18228177786287551882580827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97216948193533610040431077 18228177786287551882580827)
    ·
      refine ⟨27342266679431327823871241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18228177786287551882580827 27342266679431327823871241)
      ·
        refine ⟨20506700009573495867903431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27342266679431327823871241 20506700009573495867903431)
        ·
          refine ⟨30760050014360243801855147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20506700009573495867903431 30760050014360243801855147)
          ·
            refine ⟨46140075021540365702782721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30760050014360243801855147 46140075021540365702782721)
            ·
              refine ⟨34605056266155274277087041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46140075021540365702782721 34605056266155274277087041)
              ·
                refine ⟨25953792199616455707815281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34605056266155274277087041 25953792199616455707815281)
                ·
                  refine ⟨19465344149712341780861461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25953792199616455707815281 19465344149712341780861461)
                  ·
                    refine ⟨912438007017766020977881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19465344149712341780861461 912438007017766020977881)
                    ·
                      rfl

theorem cell23_5330900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_5330900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330900 prefixEnd_5330900 := by exact prefixLift 5330900
  have htrace : WordTrace (prefixWord ++ tailWord_5330900) baseStart_5330900 baseEnd_5330900 := by
    simpa [prefixWord, tailWord_5330900, baseEnd_5330900] using wordTrace_append hprefix tailTrace_5330900
  have hstable : (prefixWord ++ tailWord_5330900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330900).length < 2 ^ (prefixWord ++ tailWord_5330900).sum := by decide
  have hdescent : baseEnd_5330900 < baseStart_5330900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330902 : List Nat := [5, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_5330902 : Nat := 118140960795 + 5330902 * 2 ^ 59
def prefixEnd_5330902 : Nat := 4983230072969 + 3 ^ 40 * 5330902 * 2
def baseEnd_5330902 : Nat := 2737315048014607055108635

theorem tailTrace_5330902 : CollatzResearch.WordTrace tailWord_5330902 prefixEnd_5330902 2737315048014607055108635 := by
  unfold tailWord_5330902
  simp only [CollatzResearch.WordTrace]
  refine ⟨12152123083316248401402185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129622646222039982948289973 12152123083316248401402185)
  ·
    refine ⟨9114092312487186301051639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12152123083316248401402185 9114092312487186301051639)
    ·
      refine ⟨13671138468730779451577459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9114092312487186301051639 13671138468730779451577459)
      ·
        refine ⟨20506707703096169177366189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13671138468730779451577459 20506707703096169177366189)
        ·
          refine ⟨7690015388661063441512321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20506707703096169177366189 7690015388661063441512321)
          ·
            refine ⟨5767511541495797581134241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7690015388661063441512321 5767511541495797581134241)
            ·
              refine ⟨4325633656121848185850681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5767511541495797581134241 4325633656121848185850681)
              ·
                refine ⟨3244225242091386139388011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4325633656121848185850681 3244225242091386139388011)
                ·
                  refine ⟨4866337863137079209082017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3244225242091386139388011 4866337863137079209082017)
                  ·
                    refine ⟨3649753397352809406811513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4866337863137079209082017 3649753397352809406811513)
                    ·
                      refine ⟨2737315048014607055108635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3649753397352809406811513 2737315048014607055108635)
                      ·
                        rfl

theorem cell23_5330902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_5330902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330902 prefixEnd_5330902 := by exact prefixLift 5330902
  have htrace : WordTrace (prefixWord ++ tailWord_5330902) baseStart_5330902 baseEnd_5330902 := by
    simpa [prefixWord, tailWord_5330902, baseEnd_5330902] using wordTrace_append hprefix tailTrace_5330902
  have hstable : (prefixWord ++ tailWord_5330902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330902).length < 2 ^ (prefixWord ++ tailWord_5330902).sum := by decide
  have hdescent : baseEnd_5330902 < baseStart_5330902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330940 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 1, 5, 3]
def baseStart_5330940 : Nat := 118140960795 + 5330940 * 2 ^ 59
def prefixEnd_5330940 : Nat := 4983230072969 + 3 ^ 40 * 5330940 * 2
def baseEnd_5330940 : Nat := 2737334560279477906433459

theorem tailTrace_5330940 : CollatzResearch.WordTrace tailWord_5330940 prefixEnd_5330940 2737334560279477906433459 := by
  unfold tailWord_5330940
  simp only [CollatzResearch.WordTrace]
  refine ⟨97217677653461153456159137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129623570204614871274878849 97217677653461153456159137)
  ·
    refine ⟨72913258240095865092119353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97217677653461153456159137 72913258240095865092119353)
    ·
      refine ⟨54684943680071898819089515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72913258240095865092119353 54684943680071898819089515)
      ·
        refine ⟨82027415520107848228634273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54684943680071898819089515 82027415520107848228634273)
        ·
          refine ⟨61520561640080886171475705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82027415520107848228634273 61520561640080886171475705)
          ·
            refine ⟨46140421230060664628606779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61520561640080886171475705 46140421230060664628606779)
            ·
              refine ⟨69210631845090996942910169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46140421230060664628606779 69210631845090996942910169)
              ·
                refine ⟨51907973883818247707182627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69210631845090996942910169 51907973883818247707182627)
                ·
                  refine ⟨77861960825727371560773941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51907973883818247707182627 77861960825727371560773941)
                  ·
                    refine ⟨7299558827411941083822557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77861960825727371560773941 7299558827411941083822557)
                    ·
                      refine ⟨2737334560279477906433459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7299558827411941083822557 2737334560279477906433459)
                      ·
                        rfl

theorem cell23_5330940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_5330940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330940 prefixEnd_5330940 := by exact prefixLift 5330940
  have htrace : WordTrace (prefixWord ++ tailWord_5330940) baseStart_5330940 baseEnd_5330940 := by
    simpa [prefixWord, tailWord_5330940, baseEnd_5330940] using wordTrace_append hprefix tailTrace_5330940
  have hstable : (prefixWord ++ tailWord_5330940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330940).length < 2 ^ (prefixWord ++ tailWord_5330940).sum := by decide
  have hdescent : baseEnd_5330940 < baseStart_5330940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5330997 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 1, 6, 2]
def baseStart_5330997 : Nat := 118140960795 + 5330997 * 2 ^ 59
def prefixEnd_5330997 : Nat := 4983230072969 + 3 ^ 40 * 5330997 * 2
def baseEnd_5330997 : Nat := 2737363828676784183420697

theorem tailTrace_5330997 : CollatzResearch.WordTrace tailWord_5330997 prefixEnd_5330997 2737363828676784183420697 := by
  unfold tailWord_5330997
  simp only [CollatzResearch.WordTrace]
  refine ⟨194437434267715805647143245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129624956178477203764762163 194437434267715805647143245)
  ·
    refine ⟨72914037850393427117678717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194437434267715805647143245 72914037850393427117678717)
    ·
      refine ⟨27342764193897535169129519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72914037850393427117678717 27342764193897535169129519)
      ·
        refine ⟨41014146290846302753694279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27342764193897535169129519 41014146290846302753694279)
        ·
          refine ⟨61521219436269454130541419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41014146290846302753694279 61521219436269454130541419)
          ·
            refine ⟨92281829154404181195812129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61521219436269454130541419 92281829154404181195812129)
            ·
              refine ⟨69211371865803135896859097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92281829154404181195812129 69211371865803135896859097)
              ·
                refine ⟨51908528899352351922644323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69211371865803135896859097 51908528899352351922644323)
                ·
                  refine ⟨77862793349028527883966485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51908528899352351922644323 77862793349028527883966485)
                  ·
                    refine ⟨3649818438235712244560929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77862793349028527883966485 3649818438235712244560929)
                    ·
                      refine ⟨2737363828676784183420697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3649818438235712244560929 2737363828676784183420697)
                      ·
                        rfl

theorem cell23_5330997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_5330997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5330997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5330997 prefixEnd_5330997 := by exact prefixLift 5330997
  have htrace : WordTrace (prefixWord ++ tailWord_5330997) baseStart_5330997 baseEnd_5330997 := by
    simpa [prefixWord, tailWord_5330997, baseEnd_5330997] using wordTrace_append hprefix tailTrace_5330997
  have hstable : (prefixWord ++ tailWord_5330997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5330997).length < 2 ^ (prefixWord ++ tailWord_5330997).sum := by decide
  have hdescent : baseEnd_5330997 < baseStart_5330997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5330997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331017 : List Nat := [1, 2, 1, 1, 2, 2, 5, 2, 2, 2, 3]
def baseStart_5331017 : Nat := 118140960795 + 5331017 * 2 ^ 59
def prefixEnd_5331017 : Nat := 4983230072969 + 3 ^ 40 * 5331017 * 2
def baseEnd_5331017 : Nat := 2737374098289874105170605

theorem tailTrace_5331017 : CollatzResearch.WordTrace tailWord_5331017 prefixEnd_5331017 2737374098289874105170605 := by
  unfold tailWord_5331017
  simp only [CollatzResearch.WordTrace]
  refine ⟨194438163727643349062871305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129625442485095566041914203 194438163727643349062871305)
  ·
    refine ⟨145828622795732511797153479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194438163727643349062871305 145828622795732511797153479)
    ·
      refine ⟨218742934193598767695730219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145828622795732511797153479 218742934193598767695730219)
      ·
        refine ⟨328114401290398151543595329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218742934193598767695730219 328114401290398151543595329)
        ·
          refine ⟨246085800967798613657696497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328114401290398151543595329 246085800967798613657696497)
          ·
            refine ⟨184564350725848960243272373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246085800967798613657696497 184564350725848960243272373)
            ·
              refine ⟨17302907880548340022806785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184564350725848960243272373 17302907880548340022806785)
              ·
                refine ⟨12977180910411255017105089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17302907880548340022806785 12977180910411255017105089)
                ·
                  refine ⟨9732885682808441262828817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12977180910411255017105089 9732885682808441262828817)
                  ·
                    refine ⟨7299664262106330947121613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9732885682808441262828817 7299664262106330947121613)
                    ·
                      refine ⟨2737374098289874105170605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7299664262106330947121613 2737374098289874105170605)
                      ·
                        rfl

theorem cell23_5331017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 2, 3].length) (baseStart_5331017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331017 prefixEnd_5331017 := by exact prefixLift 5331017
  have htrace : WordTrace (prefixWord ++ tailWord_5331017) baseStart_5331017 baseEnd_5331017 := by
    simpa [prefixWord, tailWord_5331017, baseEnd_5331017] using wordTrace_append hprefix tailTrace_5331017
  have hstable : (prefixWord ++ tailWord_5331017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331017).length < 2 ^ (prefixWord ++ tailWord_5331017).sum := by decide
  have hdescent : baseEnd_5331017 < baseStart_5331017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331020 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 8]
def baseStart_5331020 : Nat := 118140960795 + 5331020 * 2 ^ 59
def prefixEnd_5331020 : Nat := 4983230072969 + 3 ^ 40 * 5331020 * 2
def baseEnd_5331020 : Nat := 304152848747981954825899

theorem tailTrace_5331020 : CollatzResearch.WordTrace tailWord_5331020 prefixEnd_5331020 304152848747981954825899 := by
  unfold tailWord_5331020
  simp only [CollatzResearch.WordTrace]
  refine ⟨97219136573316240287615257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129625515431088320383487009 97219136573316240287615257)
  ·
    refine ⟨72914352429987180215711443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97219136573316240287615257 72914352429987180215711443)
    ·
      refine ⟨109371528644980770323567165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72914352429987180215711443 109371528644980770323567165)
      ·
        refine ⟨41014323241867788871337687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109371528644980770323567165 41014323241867788871337687)
        ·
          refine ⟨61521484862801683307006531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41014323241867788871337687 61521484862801683307006531)
          ·
            refine ⟨92282227294202524960509797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61521484862801683307006531 92282227294202524960509797)
            ·
              refine ⟨17302917617662973430095587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92282227294202524960509797 17302917617662973430095587)
              ·
                refine ⟨25954376426494460145143381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17302917617662973430095587 25954376426494460145143381)
                ·
                  refine ⟨304152848747981954825899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25954376426494460145143381 304152848747981954825899)
                  ·
                    rfl

theorem cell23_5331020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 8].length) (baseStart_5331020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331020 prefixEnd_5331020 := by exact prefixLift 5331020
  have htrace : WordTrace (prefixWord ++ tailWord_5331020) baseStart_5331020 baseEnd_5331020 := by
    simpa [prefixWord, tailWord_5331020, baseEnd_5331020] using wordTrace_append hprefix tailTrace_5331020
  have hstable : (prefixWord ++ tailWord_5331020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331020).length < 2 ^ (prefixWord ++ tailWord_5331020).sum := by decide
  have hdescent : baseEnd_5331020 < baseStart_5331020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331081 : List Nat := [1, 2, 1, 1, 4, 2, 3, 4, 1, 1, 3]
def baseStart_5331081 : Nat := 118140960795 + 5331081 * 2 ^ 59
def prefixEnd_5331081 : Nat := 4983230072969 + 3 ^ 40 * 5331081 * 2
def baseEnd_5331081 : Nat := 2737406961051761854770311

theorem tailTrace_5331081 : CollatzResearch.WordTrace tailWord_5331081 prefixEnd_5331081 2737406961051761854770311 := by
  unfold tailWord_5331081
  simp only [CollatzResearch.WordTrace]
  refine ⟨194440497999411487993201097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129626998666274325328800731 194440497999411487993201097)
  ·
    refine ⟨145830373499558615994900823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194440497999411487993201097 145830373499558615994900823)
    ·
      refine ⟨218745560249337923992351235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145830373499558615994900823 218745560249337923992351235)
      ·
        refine ⟨328118340374006885988526853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218745560249337923992351235 328118340374006885988526853)
        ·
          refine ⟨61522188820126291122848785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 328118340374006885988526853 61522188820126291122848785)
          ·
            refine ⟨46141641615094718342136589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61522188820126291122848785 46141641615094718342136589)
            ·
              refine ⟨17303115605660519378301221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46141641615094718342136589 17303115605660519378301221)
              ·
                refine ⟨3244334176061347383431479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17303115605660519378301221 3244334176061347383431479)
                ·
                  refine ⟨4866501264092021075147219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3244334176061347383431479 4866501264092021075147219)
                  ·
                    refine ⟨7299751896138031612720829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4866501264092021075147219 7299751896138031612720829)
                    ·
                      refine ⟨2737406961051761854770311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7299751896138031612720829 2737406961051761854770311)
                      ·
                        rfl

theorem cell23_5331081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 1, 1, 3].length) (baseStart_5331081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331081 prefixEnd_5331081 := by exact prefixLift 5331081
  have htrace : WordTrace (prefixWord ++ tailWord_5331081) baseStart_5331081 baseEnd_5331081 := by
    simpa [prefixWord, tailWord_5331081, baseEnd_5331081] using wordTrace_append hprefix tailTrace_5331081
  have hstable : (prefixWord ++ tailWord_5331081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331081).length < 2 ^ (prefixWord ++ tailWord_5331081).sum := by decide
  have hdescent : baseEnd_5331081 < baseStart_5331081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331108 : List Nat := [2, 3, 1, 2, 4, 2, 1, 1, 2, 3, 2]
def baseStart_5331108 : Nat := 118140960795 + 5331108 * 2 ^ 59
def prefixEnd_5331108 : Nat := 4983230072969 + 3 ^ 40 * 5331108 * 2
def baseEnd_5331108 : Nat := 2737420825029433249132687

theorem tailTrace_5331108 : CollatzResearch.WordTrace tailWord_5331108 prefixEnd_5331108 2737420825029433249132687 := by
  unfold tailWord_5331108
  simp only [CollatzResearch.WordTrace]
  refine ⟨97220741385156835802216989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129627655180209114402955985 97220741385156835802216989)
  ·
    refine ⟨36457778019433813425831371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97220741385156835802216989 36457778019433813425831371)
    ·
      refine ⟨54686667029150720138747057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36457778019433813425831371 54686667029150720138747057)
      ·
        refine ⟨41015000271863040104060293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54686667029150720138747057 41015000271863040104060293)
        ·
          refine ⟨7690312550974320019511305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41015000271863040104060293 7690312550974320019511305)
          ·
            refine ⟨5767734413230740014633479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7690312550974320019511305 5767734413230740014633479)
            ·
              refine ⟨8651601619846110021950219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5767734413230740014633479 8651601619846110021950219)
              ·
                refine ⟨12977402429769165032925329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8651601619846110021950219 12977402429769165032925329)
                ·
                  refine ⟨9733051822326873774693997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12977402429769165032925329 9733051822326873774693997)
                  ·
                    refine ⟨3649894433372577665510249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9733051822326873774693997 3649894433372577665510249)
                    ·
                      refine ⟨2737420825029433249132687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3649894433372577665510249 2737420825029433249132687)
                      ·
                        rfl

theorem cell23_5331108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_5331108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331108 prefixEnd_5331108 := by exact prefixLift 5331108
  have htrace : WordTrace (prefixWord ++ tailWord_5331108) baseStart_5331108 baseEnd_5331108 := by
    simpa [prefixWord, tailWord_5331108, baseEnd_5331108] using wordTrace_append hprefix tailTrace_5331108
  have hstable : (prefixWord ++ tailWord_5331108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331108).length < 2 ^ (prefixWord ++ tailWord_5331108).sum := by decide
  have hdescent : baseEnd_5331108 < baseStart_5331108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331118 : List Nat := [4, 1, 4, 2, 1, 1, 1, 3, 1, 5]
def baseStart_5331118 : Nat := 118140960795 + 5331118 * 2 ^ 59
def prefixEnd_5331118 : Nat := 4983230072969 + 3 ^ 40 * 5331118 * 2
def baseEnd_5331118 : Nat := 912475319945326070002547

theorem tailTrace_5331118 : CollatzResearch.WordTrace tailWord_5331118 prefixEnd_5331118 912475319945326070002547 := by
  unfold tailWord_5331118
  simp only [CollatzResearch.WordTrace]
  refine ⟨24305230937534680414037251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129627898333518295541532005 24305230937534680414037251)
  ·
    refine ⟨36457846406302020621055877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24305230937534680414037251 36457846406302020621055877)
    ·
      refine ⟨6835846201181628866447977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36457846406302020621055877 6835846201181628866447977)
      ·
        refine ⟨5126884650886221649835983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6835846201181628866447977 5126884650886221649835983)
        ·
          refine ⟨7690326976329332474753975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5126884650886221649835983 7690326976329332474753975)
          ·
            refine ⟨11535490464493998712130963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7690326976329332474753975 11535490464493998712130963)
            ·
              refine ⟨17303235696740998068196445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11535490464493998712130963 17303235696740998068196445)
              ·
                refine ⟨6488713386277874275573667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17303235696740998068196445 6488713386277874275573667)
                ·
                  refine ⟨9733070079416811413360501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6488713386277874275573667 9733070079416811413360501)
                  ·
                    refine ⟨912475319945326070002547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9733070079416811413360501 912475319945326070002547)
                    ·
                      rfl

theorem cell23_5331118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_5331118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331118 prefixEnd_5331118 := by exact prefixLift 5331118
  have htrace : WordTrace (prefixWord ++ tailWord_5331118) baseStart_5331118 baseEnd_5331118 := by
    simpa [prefixWord, tailWord_5331118, baseEnd_5331118] using wordTrace_append hprefix tailTrace_5331118
  have hstable : (prefixWord ++ tailWord_5331118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331118).length < 2 ^ (prefixWord ++ tailWord_5331118).sum := by decide
  have hdescent : baseEnd_5331118 < baseStart_5331118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331121 : List Nat := [1, 2, 2, 5, 2, 1, 1, 3, 1, 1, 4]
def baseStart_5331121 : Nat := 118140960795 + 5331121 * 2 ^ 59
def prefixEnd_5331121 : Nat := 4983230072969 + 3 ^ 40 * 5331121 * 2
def baseEnd_5331121 : Nat := 2737427500277941698270127

theorem tailTrace_5331121 : CollatzResearch.WordTrace tailWord_5331121 prefixEnd_5331121 2737427500277941698270127 := by
  unfold tailWord_5331121
  simp only [CollatzResearch.WordTrace]
  refine ⟨194441956919266574824657217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129627971279511049883104811 194441956919266574824657217)
  ·
    refine ⟨145831467689449931118492913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194441956919266574824657217 145831467689449931118492913)
    ·
      refine ⟨109373600767087448338869685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145831467689449931118492913 109373600767087448338869685)
      ·
        refine ⟨10253775071914448281769033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109373600767087448338869685 10253775071914448281769033)
        ·
          refine ⟨7690331303935836211326775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10253775071914448281769033 7690331303935836211326775)
          ·
            refine ⟨11535496955903754316990163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7690331303935836211326775 11535496955903754316990163)
            ·
              refine ⟨17303245433855631475485245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11535496955903754316990163 17303245433855631475485245)
              ·
                refine ⟨6488717037695861803306967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17303245433855631475485245 6488717037695861803306967)
                ·
                  refine ⟨9733075556543792704960451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6488717037695861803306967 9733075556543792704960451)
                  ·
                    refine ⟨14599613334815689057440677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9733075556543792704960451 14599613334815689057440677)
                    ·
                      refine ⟨2737427500277941698270127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14599613334815689057440677 2737427500277941698270127)
                      ·
                        rfl

theorem cell23_5331121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_5331121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331121 prefixEnd_5331121 := by exact prefixLift 5331121
  have htrace : WordTrace (prefixWord ++ tailWord_5331121) baseStart_5331121 baseEnd_5331121 := by
    simpa [prefixWord, tailWord_5331121, baseEnd_5331121] using wordTrace_append hprefix tailTrace_5331121
  have hstable : (prefixWord ++ tailWord_5331121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331121).length < 2 ^ (prefixWord ++ tailWord_5331121).sum := by decide
  have hdescent : baseEnd_5331121 < baseStart_5331121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331148 : List Nat := [2, 2, 1, 6, 2, 1, 1, 1, 1, 6]
def baseStart_5331148 : Nat := 118140960795 + 5331148 * 2 ^ 59
def prefixEnd_5331148 : Nat := 4983230072969 + 3 ^ 40 * 5331148 * 2
def baseEnd_5331148 : Nat := 912480454751871030877501

theorem tailTrace_5331148 : CollatzResearch.WordTrace tailWord_5331148 prefixEnd_5331148 912480454751871030877501 := by
  unfold tailWord_5331148
  simp only [CollatzResearch.WordTrace]
  refine ⟨97221470845084379217945049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129628627793445838957260065 97221470845084379217945049)
  ·
    refine ⟨72916103133813284413458787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97221470845084379217945049 72916103133813284413458787)
    ·
      refine ⟨109374154700719926620188181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72916103133813284413458787 109374154700719926620188181)
      ·
        refine ⟨5126913501596246560321321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 109374154700719926620188181 5126913501596246560321321)
        ·
          refine ⟨3845185126197184920240991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5126913501596246560321321 3845185126197184920240991)
          ·
            refine ⟨5767777689295777380361487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3845185126197184920240991 5767777689295777380361487)
            ·
              refine ⟨8651666533943666070542231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5767777689295777380361487 8651666533943666070542231)
              ·
                refine ⟨12977499800915499105813347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8651666533943666070542231 12977499800915499105813347)
                ·
                  refine ⟨19466249701373248658720021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12977499800915499105813347 19466249701373248658720021)
                  ·
                    refine ⟨912480454751871030877501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19466249701373248658720021 912480454751871030877501)
                    ·
                      rfl

theorem cell23_5331148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 1, 6].length) (baseStart_5331148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331148 prefixEnd_5331148 := by exact prefixLift 5331148
  have htrace : WordTrace (prefixWord ++ tailWord_5331148) baseStart_5331148 baseEnd_5331148 := by
    simpa [prefixWord, tailWord_5331148, baseEnd_5331148] using wordTrace_append hprefix tailTrace_5331148
  have hstable : (prefixWord ++ tailWord_5331148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331148).length < 2 ^ (prefixWord ++ tailWord_5331148).sum := by decide
  have hdescent : baseEnd_5331148 < baseStart_5331148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331158 : List Nat := [5, 2, 1, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_5331158 : Nat := 118140960795 + 5331158 * 2 ^ 59
def prefixEnd_5331158 : Nat := 4983230072969 + 3 ^ 40 * 5331158 * 2
def baseEnd_5331158 : Nat := 2737446499062158053507457

theorem tailTrace_5331158 : CollatzResearch.WordTrace tailWord_5331158 prefixEnd_5331158 2737446499062158053507457 := by
  unfold tailWord_5331158
  simp only [CollatzResearch.WordTrace]
  refine ⟨12152706651258283133984633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129628870946755020095836085 12152706651258283133984633)
  ·
    refine ⟨9114529988443712350488475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12152706651258283133984633 9114529988443712350488475)
    ·
      refine ⟨13671794982665568525732713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9114529988443712350488475 13671794982665568525732713)
      ·
        refine ⟨10253846236999176394299535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13671794982665568525732713 10253846236999176394299535)
        ·
          refine ⟨15380769355498764591449303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10253846236999176394299535 15380769355498764591449303)
          ·
            refine ⟨23071154033248146887173955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15380769355498764591449303 23071154033248146887173955)
            ·
              refine ⟨34606731049872220330760933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23071154033248146887173955 34606731049872220330760933)
              ·
                refine ⟨6488762071851041312017675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34606731049872220330760933 6488762071851041312017675)
                ·
                  refine ⟨9733143107776561968026513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6488762071851041312017675 9733143107776561968026513)
                  ·
                    refine ⟨7299857330832421476019885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9733143107776561968026513 7299857330832421476019885)
                    ·
                      refine ⟨2737446499062158053507457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7299857330832421476019885 2737446499062158053507457)
                      ·
                        rfl

theorem cell23_5331158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_5331158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331158 prefixEnd_5331158 := by exact prefixLift 5331158
  have htrace : WordTrace (prefixWord ++ tailWord_5331158) baseStart_5331158 baseEnd_5331158 := by
    simpa [prefixWord, tailWord_5331158, baseEnd_5331158] using wordTrace_append hprefix tailTrace_5331158
  have hstable : (prefixWord ++ tailWord_5331158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331158).length < 2 ^ (prefixWord ++ tailWord_5331158).sum := by decide
  have hdescent : baseEnd_5331158 < baseStart_5331158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331281 : List Nat := [1, 2, 2, 1, 4, 4, 1, 1, 2, 5]
def baseStart_5331281 : Nat := 118140960795 + 5331281 * 2 ^ 59
def prefixEnd_5331281 : Nat := 4983230072969 + 3 ^ 40 * 5331281 * 2
def baseEnd_5331281 : Nat := 912503219060887024089797

theorem tailTrace_5331281 : CollatzResearch.WordTrace tailWord_5331281 prefixEnd_5331281 912503219060887024089797 := by
  unfold tailWord_5331281
  simp only [CollatzResearch.WordTrace]
  refine ⟨194447792598686922150481697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129631861732457948100321131 194447792598686922150481697)
  ·
    refine ⟨145835844449015191612861273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194447792598686922150481697 145835844449015191612861273)
    ·
      refine ⟨109376883336761393709645955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145835844449015191612861273 109376883336761393709645955)
      ·
        refine ⟨164065325005142090564468933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109376883336761393709645955 164065325005142090564468933)
        ·
          refine ⟨30762248438464141980837925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164065325005142090564468933 30762248438464141980837925)
          ·
            refine ⟨5767921582212026621407111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30762248438464141980837925 5767921582212026621407111)
            ·
              refine ⟨8651882373318039932110667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5767921582212026621407111 8651882373318039932110667)
              ·
                refine ⟨12977823559977059898166001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8651882373318039932110667 12977823559977059898166001)
                ·
                  refine ⟨9733367669982794923624501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12977823559977059898166001 9733367669982794923624501)
                  ·
                    refine ⟨912503219060887024089797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9733367669982794923624501 912503219060887024089797)
                    ·
                      rfl

theorem cell23_5331281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_5331281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331281 prefixEnd_5331281 := by exact prefixLift 5331281
  have htrace : WordTrace (prefixWord ++ tailWord_5331281) baseStart_5331281 baseEnd_5331281 := by
    simpa [prefixWord, tailWord_5331281, baseEnd_5331281] using wordTrace_append hprefix tailTrace_5331281
  have hstable : (prefixWord ++ tailWord_5331281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331281).length < 2 ^ (prefixWord ++ tailWord_5331281).sum := by decide
  have hdescent : baseEnd_5331281 < baseStart_5331281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331301 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 2, 4, 2]
def baseStart_5331301 : Nat := 118140960795 + 5331301 * 2 ^ 59
def prefixEnd_5331301 : Nat := 4983230072969 + 3 ^ 40 * 5331301 * 2
def baseEnd_5331301 : Nat := 2737519926795750994019299

theorem tailTrace_5331301 : CollatzResearch.WordTrace tailWord_5331301 prefixEnd_5331301 2737519926795750994019299 := by
  unfold tailWord_5331301
  simp only [CollatzResearch.WordTrace]
  refine ⟨194448522058614465566209757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129632348039076310377473171 194448522058614465566209757)
  ·
    refine ⟨72918195771980424587328659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194448522058614465566209757 72918195771980424587328659)
    ·
      refine ⟨109377293657970636880992989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72918195771980424587328659 109377293657970636880992989)
      ·
        refine ⟨41016485121738988830372371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109377293657970636880992989 41016485121738988830372371)
        ·
          refine ⟨61524727682608483245558557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41016485121738988830372371 61524727682608483245558557)
          ·
            refine ⟨23071772880978181217084459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61524727682608483245558557 23071772880978181217084459)
            ·
              refine ⟨34607659321467271825626689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23071772880978181217084459 34607659321467271825626689)
              ·
                refine ⟨25955744491100453869220017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34607659321467271825626689 25955744491100453869220017)
                ·
                  refine ⟨19466808368325340401915013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25955744491100453869220017 19466808368325340401915013)
                  ·
                    refine ⟨3650026569061001325359065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19466808368325340401915013 3650026569061001325359065)
                    ·
                      refine ⟨2737519926795750994019299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3650026569061001325359065 2737519926795750994019299)
                      ·
                        rfl

theorem cell23_5331301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_5331301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331301 prefixEnd_5331301 := by exact prefixLift 5331301
  have htrace : WordTrace (prefixWord ++ tailWord_5331301) baseStart_5331301 baseEnd_5331301 := by
    simpa [prefixWord, tailWord_5331301, baseEnd_5331301] using wordTrace_append hprefix tailTrace_5331301
  have hstable : (prefixWord ++ tailWord_5331301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331301).length < 2 ^ (prefixWord ++ tailWord_5331301).sum := by decide
  have hdescent : baseEnd_5331301 < baseStart_5331301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331307 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 8]
def baseStart_5331307 : Nat := 118140960795 + 5331307 * 2 ^ 59
def prefixEnd_5331307 : Nat := 4983230072969 + 3 ^ 40 * 5331307 * 2
def baseEnd_5331307 : Nat := 304169223075519774504919

theorem tailTrace_5331307 : CollatzResearch.WordTrace tailWord_5331307 prefixEnd_5331307 304169223075519774504919 := by
  unfold tailWord_5331307
  simp only [CollatzResearch.WordTrace]
  refine ⟨194448740896592728590928175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129632493931061819060618783 194448740896592728590928175)
  ·
    refine ⟨291673111344889092886392263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194448740896592728590928175 291673111344889092886392263)
    ·
      refine ⟨437509667017333639329588395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291673111344889092886392263 437509667017333639329588395)
      ·
        refine ⟨656264500526000458994382593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437509667017333639329588395 656264500526000458994382593)
        ·
          refine ⟨492198375394500344245786945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 656264500526000458994382593 492198375394500344245786945)
          ·
            refine ⟨369148781545875258184340209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 492198375394500344245786945 369148781545875258184340209)
            ·
              refine ⟨276861586159406443638255157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369148781545875258184340209 276861586159406443638255157)
              ·
                refine ⟨25955773702444354091086421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 276861586159406443638255157 25955773702444354091086421)
                ·
                  refine ⟨304169223075519774504919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25955773702444354091086421 304169223075519774504919)
                  ·
                    rfl

theorem cell23_5331307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 8].length) (baseStart_5331307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331307 prefixEnd_5331307 := by exact prefixLift 5331307
  have htrace : WordTrace (prefixWord ++ tailWord_5331307) baseStart_5331307 baseEnd_5331307 := by
    simpa [prefixWord, tailWord_5331307, baseEnd_5331307] using wordTrace_append hprefix tailTrace_5331307
  have hstable : (prefixWord ++ tailWord_5331307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331307).length < 2 ^ (prefixWord ++ tailWord_5331307).sum := by decide
  have hdescent : baseEnd_5331307 < baseStart_5331307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331351 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 5, 1, 3]
def baseStart_5331351 : Nat := 118140960795 + 5331351 * 2 ^ 59
def prefixEnd_5331351 : Nat := 4983230072969 + 3 ^ 40 * 5331351 * 2
def baseEnd_5331351 : Nat := 2737545600828475798394069

theorem tailTrace_5331351 : CollatzResearch.WordTrace tailWord_5331351 prefixEnd_5331351 2737545600828475798394069 := by
  unfold tailWord_5331351
  simp only [CollatzResearch.WordTrace]
  refine ⟨194450345708433324105529907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129633563805622216070353271 194450345708433324105529907)
  ·
    refine ⟨291675518562649986158294861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194450345708433324105529907 291675518562649986158294861)
    ·
      refine ⟨109378319460993744809360573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291675518562649986158294861 109378319460993744809360573)
      ·
        refine ⟨41016869797872654303510215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109378319460993744809360573 41016869797872654303510215)
        ·
          refine ⟨61525304696808981455265323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41016869797872654303510215 61525304696808981455265323)
          ·
            refine ⟨92287957045213472182897985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61525304696808981455265323 92287957045213472182897985)
            ·
              refine ⟨69215967783910104137173489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92287957045213472182897985 69215967783910104137173489)
              ·
                refine ⟨51911975837932578102880117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69215967783910104137173489 51911975837932578102880117)
                ·
                  refine ⟨4866747734806179197145011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51911975837932578102880117 4866747734806179197145011)
                  ·
                    refine ⟨7300121602209268795717517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4866747734806179197145011 7300121602209268795717517)
                    ·
                      refine ⟨2737545600828475798394069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7300121602209268795717517 2737545600828475798394069)
                      ·
                        rfl

theorem cell23_5331351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_5331351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331351 prefixEnd_5331351 := by exact prefixLift 5331351
  have htrace : WordTrace (prefixWord ++ tailWord_5331351) baseStart_5331351 baseEnd_5331351 := by
    simpa [prefixWord, tailWord_5331351, baseEnd_5331351] using wordTrace_append hprefix tailTrace_5331351
  have hstable : (prefixWord ++ tailWord_5331351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331351).length < 2 ^ (prefixWord ++ tailWord_5331351).sum := by decide
  have hdescent : baseEnd_5331351 < baseStart_5331351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331384 : List Nat := [2, 1, 2, 1, 2, 2, 1, 5, 1, 6]
def baseStart_5331384 : Nat := 118140960795 + 5331384 * 2 ^ 59
def prefixEnd_5331384 : Nat := 4983230072969 + 3 ^ 40 * 5331384 * 2
def baseEnd_5331384 : Nat := 912520848563358056427139

theorem tailTrace_5331384 : CollatzResearch.WordTrace tailWord_5331384 prefixEnd_5331384 912520848563358056427139 := by
  unfold tailWord_5331384
  simp only [CollatzResearch.WordTrace]
  refine ⟨97225774658656885370740603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129634366211542513827654137 97225774658656885370740603)
  ·
    refine ⟨145838661987985328056110905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97225774658656885370740603 145838661987985328056110905)
    ·
      refine ⟨109378996490988996042083179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145838661987985328056110905 109378996490988996042083179)
      ·
        refine ⟨164068494736483494063124769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109378996490988996042083179 164068494736483494063124769)
        ·
          refine ⟨123051371052362620547343577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164068494736483494063124769 123051371052362620547343577)
          ·
            refine ⟨92288528289271965410507683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123051371052362620547343577 92288528289271965410507683)
            ·
              refine ⟨138432792433907948115761525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92288528289271965410507683 138432792433907948115761525)
              ·
                refine ⟨12978074290678870135852643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138432792433907948115761525 12978074290678870135852643)
                ·
                  refine ⟨19467111436018305203778965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12978074290678870135852643 19467111436018305203778965)
                  ·
                    refine ⟨912520848563358056427139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19467111436018305203778965 912520848563358056427139)
                    ·
                      rfl

theorem cell23_5331384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_5331384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331384 prefixEnd_5331384 := by exact prefixLift 5331384
  have htrace : WordTrace (prefixWord ++ tailWord_5331384) baseStart_5331384 baseEnd_5331384 := by
    simpa [prefixWord, tailWord_5331384, baseEnd_5331384] using wordTrace_append hprefix tailTrace_5331384
  have hstable : (prefixWord ++ tailWord_5331384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331384).length < 2 ^ (prefixWord ++ tailWord_5331384).sum := by decide
  have hdescent : baseEnd_5331384 < baseStart_5331384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331388 : List Nat := [2, 2, 2, 4, 1, 1, 3, 2, 1, 5]
def baseStart_5331388 : Nat := 118140960795 + 5331388 * 2 ^ 59
def prefixEnd_5331388 : Nat := 4983230072969 + 3 ^ 40 * 5331388 * 2
def baseEnd_5331388 : Nat := 912521533204230717877133

theorem tailTrace_5331388 : CollatzResearch.WordTrace tailWord_5331388 prefixEnd_5331388 912521533204230717877133 := by
  unfold tailWord_5331388
  simp only [CollatzResearch.WordTrace]
  refine ⟨97225847604649639712313409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129634463472866186283084545 97225847604649639712313409)
  ·
    refine ⟨72919385703487229784235057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97225847604649639712313409 72919385703487229784235057)
    ·
      refine ⟨54689539277615422338176293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72919385703487229784235057 54689539277615422338176293)
      ·
        refine ⟨10254288614552891688408055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54689539277615422338176293 10254288614552891688408055)
        ·
          refine ⟨15381432921829337532612083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10254288614552891688408055 15381432921829337532612083)
          ·
            refine ⟨23072149382744006298918125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15381432921829337532612083 23072149382744006298918125)
            ·
              refine ⟨8652056018529002362094297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23072149382744006298918125 8652056018529002362094297)
              ·
                refine ⟨6489042013896751771570723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8652056018529002362094297 6489042013896751771570723)
                ·
                  refine ⟨9733563020845127657356085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6489042013896751771570723 9733563020845127657356085)
                  ·
                    refine ⟨912521533204230717877133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9733563020845127657356085 912521533204230717877133)
                    ·
                      rfl

theorem cell23_5331388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_5331388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331388 prefixEnd_5331388 := by exact prefixLift 5331388
  have htrace : WordTrace (prefixWord ++ tailWord_5331388) baseStart_5331388 baseEnd_5331388 := by
    simpa [prefixWord, tailWord_5331388, baseEnd_5331388] using wordTrace_append hprefix tailTrace_5331388
  have hstable : (prefixWord ++ tailWord_5331388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331388).length < 2 ^ (prefixWord ++ tailWord_5331388).sum := by decide
  have hdescent : baseEnd_5331388 < baseStart_5331388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331418 : List Nat := [3, 1, 1, 2, 3, 1, 4, 2, 2, 4]
def baseStart_5331418 : Nat := 118140960795 + 5331418 * 2 ^ 59
def prefixEnd_5331418 : Nat := 4983230072969 + 3 ^ 40 * 5331418 * 2
def baseEnd_5331418 : Nat := 912526668010775678752087

theorem tailTrace_5331418 : CollatzResearch.WordTrace tailWord_5331418 prefixEnd_5331418 912526668010775678752087 := by
  unfold tailWord_5331418
  simp only [CollatzResearch.WordTrace]
  refine ⟨48613197349797648637054727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129635192932793729698812605 48613197349797648637054727)
  ·
    refine ⟨72919796024696472955582091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48613197349797648637054727 72919796024696472955582091)
    ·
      refine ⟨109379694037044709433373137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72919796024696472955582091 109379694037044709433373137)
      ·
        refine ⟨82034770527783532075029853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109379694037044709433373137 82034770527783532075029853)
        ·
          refine ⟨30763038947918824528136195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82034770527783532075029853 30763038947918824528136195)
          ·
            refine ⟨46144558421878236792204293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30763038947918824528136195 46144558421878236792204293)
            ·
              refine ⟨8652104704102169398538305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46144558421878236792204293 8652104704102169398538305)
              ·
                refine ⟨6489078528076627048903729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8652104704102169398538305 6489078528076627048903729)
                ·
                  refine ⟨4866808896057470286677797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6489078528076627048903729 4866808896057470286677797)
                  ·
                    refine ⟨912526668010775678752087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4866808896057470286677797 912526668010775678752087)
                    ·
                      rfl

theorem cell23_5331418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_5331418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331418 prefixEnd_5331418 := by exact prefixLift 5331418
  have htrace : WordTrace (prefixWord ++ tailWord_5331418) baseStart_5331418 baseEnd_5331418 := by
    simpa [prefixWord, tailWord_5331418, baseEnd_5331418] using wordTrace_append hprefix tailTrace_5331418
  have hstable : (prefixWord ++ tailWord_5331418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331418).length < 2 ^ (prefixWord ++ tailWord_5331418).sum := by decide
  have hdescent : baseEnd_5331418 < baseStart_5331418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331421 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_5331421 : Nat := 118140960795 + 5331421 * 2 ^ 59
def prefixEnd_5331421 : Nat := 4983230072969 + 3 ^ 40 * 5331421 * 2
def baseEnd_5331421 : Nat := 2737581544474290524518747

theorem tailTrace_5331421 : CollatzResearch.WordTrace tailWord_5331421 prefixEnd_5331421 2737581544474290524518747 := by
  unfold tailWord_5331421
  simp only [CollatzResearch.WordTrace]
  refine ⟨194452898818179726060578117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129635265878786484040385411 194452898818179726060578117)
  ·
    refine ⟨36459918528408698636358397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194452898818179726060578117 36459918528408698636358397)
    ·
      refine ⟨13672469448153261988634399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36459918528408698636358397 13672469448153261988634399)
      ·
        refine ⟨20508704172229892982951599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13672469448153261988634399 20508704172229892982951599)
        ·
          refine ⟨30763056258344839474427399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20508704172229892982951599 30763056258344839474427399)
          ·
            refine ⟨46144584387517259211641099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30763056258344839474427399 46144584387517259211641099)
            ·
              refine ⟨69216876581275888817461649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46144584387517259211641099 69216876581275888817461649)
              ·
                refine ⟨51912657435956916613096237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69216876581275888817461649 51912657435956916613096237)
                ·
                  refine ⟨19467246538483843729911089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51912657435956916613096237 19467246538483843729911089)
                  ·
                    refine ⟨14600434903862882797433317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19467246538483843729911089 14600434903862882797433317)
                    ·
                      refine ⟨2737581544474290524518747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14600434903862882797433317 2737581544474290524518747)
                      ·
                        rfl

theorem cell23_5331421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_5331421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331421 prefixEnd_5331421 := by exact prefixLift 5331421
  have htrace : WordTrace (prefixWord ++ tailWord_5331421) baseStart_5331421 baseEnd_5331421 := by
    simpa [prefixWord, tailWord_5331421, baseEnd_5331421] using wordTrace_append hprefix tailTrace_5331421
  have hstable : (prefixWord ++ tailWord_5331421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331421).length < 2 ^ (prefixWord ++ tailWord_5331421).sum := by decide
  have hdescent : baseEnd_5331421 < baseStart_5331421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331438 : List Nat := [4, 1, 2, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_5331438 : Nat := 118140960795 + 5331438 * 2 ^ 59
def prefixEnd_5331438 : Nat := 4983230072969 + 3 ^ 40 * 5331438 * 2
def baseEnd_5331438 : Nat := 2737590273645416958006169

theorem tailTrace_5331438 : CollatzResearch.WordTrace tailWord_5331438 prefixEnd_5331438 2737590273645416958006169 := by
  unfold tailWord_5331438
  simp only [CollatzResearch.WordTrace]
  refine ⟨24306689857389767245493371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129635679239412091975964645 24306689857389767245493371)
  ·
    refine ⟨36460034786084650868240057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24306689857389767245493371 36460034786084650868240057)
    ·
      refine ⟨27345026089563488151180043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36460034786084650868240057 27345026089563488151180043)
      ·
        refine ⟨41017539134345232226770065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27345026089563488151180043 41017539134345232226770065)
        ·
          refine ⟨30763154350758924170077549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41017539134345232226770065 30763154350758924170077549)
          ·
            refine ⟨11536182881534596563779081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30763154350758924170077549 11536182881534596563779081)
            ·
              refine ⟨8652137161150947422834311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11536182881534596563779081 8652137161150947422834311)
              ·
                refine ⟨12978205741726421134251467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8652137161150947422834311 12978205741726421134251467)
                ·
                  refine ⟨19467308612589631701377201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12978205741726421134251467 19467308612589631701377201)
                  ·
                    refine ⟨14600481459442223776032901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19467308612589631701377201 14600481459442223776032901)
                    ·
                      refine ⟨2737590273645416958006169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14600481459442223776032901 2737590273645416958006169)
                      ·
                        rfl

theorem cell23_5331438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_5331438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331438 prefixEnd_5331438 := by exact prefixLift 5331438
  have htrace : WordTrace (prefixWord ++ tailWord_5331438) baseStart_5331438 baseEnd_5331438 := by
    simpa [prefixWord, tailWord_5331438, baseEnd_5331438] using wordTrace_append hprefix tailTrace_5331438
  have hstable : (prefixWord ++ tailWord_5331438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331438).length < 2 ^ (prefixWord ++ tailWord_5331438).sum := by decide
  have hdescent : baseEnd_5331438 < baseStart_5331438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331442 : List Nat := [3, 2, 1, 4, 2, 1, 1, 2, 3, 2, 2]
def baseStart_5331442 : Nat := 118140960795 + 5331442 * 2 ^ 59
def prefixEnd_5331442 : Nat := 4983230072969 + 3 ^ 40 * 5331442 * 2
def baseEnd_5331442 : Nat := 2737592327568034942356151

theorem tailTrace_5331442 : CollatzResearch.WordTrace tailWord_5331442 prefixEnd_5331442 2737592327568034942356151 := by
  unfold tailWord_5331442
  simp only [CollatzResearch.WordTrace]
  refine ⟨48613416187775911661773145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129635776500735764431395053 48613416187775911661773145)
  ·
    refine ⟨36460062140831933746329859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48613416187775911661773145 36460062140831933746329859)
    ·
      refine ⟨54690093211247900619494789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36460062140831933746329859 54690093211247900619494789)
      ·
        refine ⟨10254392477108981366155273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54690093211247900619494789 10254392477108981366155273)
        ·
          refine ⟨7690794357831736024616455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10254392477108981366155273 7690794357831736024616455)
          ·
            refine ⟨11536191536747604036924683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7690794357831736024616455 11536191536747604036924683)
            ·
              refine ⟨17304287305121406055387025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11536191536747604036924683 17304287305121406055387025)
              ·
                refine ⟨12978215478841054541540269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17304287305121406055387025 12978215478841054541540269)
                ·
                  refine ⟨4866830804565395453077601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12978215478841054541540269 4866830804565395453077601)
                  ·
                    refine ⟨3650123103424046589808201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4866830804565395453077601 3650123103424046589808201)
                    ·
                      refine ⟨2737592327568034942356151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3650123103424046589808201 2737592327568034942356151)
                      ·
                        rfl

theorem cell23_5331442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_5331442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331442 prefixEnd_5331442 := by exact prefixLift 5331442
  have htrace : WordTrace (prefixWord ++ tailWord_5331442) baseStart_5331442 baseEnd_5331442 := by
    simpa [prefixWord, tailWord_5331442, baseEnd_5331442] using wordTrace_append hprefix tailTrace_5331442
  have hstable : (prefixWord ++ tailWord_5331442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331442).length < 2 ^ (prefixWord ++ tailWord_5331442).sum := by decide
  have hdescent : baseEnd_5331442 < baseStart_5331442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331469 : List Nat := [1, 7, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_5331469 : Nat := 118140960795 + 5331469 * 2 ^ 59
def prefixEnd_5331469 : Nat := 4983230072969 + 3 ^ 40 * 5331469 * 2
def baseEnd_5331469 : Nat := 912535397181902112239509

theorem tailTrace_5331469 : CollatzResearch.WordTrace tailWord_5331469 prefixEnd_5331469 912535397181902112239509 := by
  unfold tailWord_5331469
  simp only [CollatzResearch.WordTrace]
  refine ⟨194454649522005830258325461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129636433014670553505550307 194454649522005830258325461)
  ·
    refine ⟨4557530848172011646679503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 194454649522005830258325461 4557530848172011646679503)
    ·
      refine ⟨6836296272258017470019255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4557530848172011646679503 6836296272258017470019255)
      ·
        refine ⟨10254444408387026205028883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6836296272258017470019255 10254444408387026205028883)
        ·
          refine ⟨15381666612580539307543325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10254444408387026205028883 15381666612580539307543325)
          ·
            refine ⟨5768124979717702240328747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15381666612580539307543325 5768124979717702240328747)
            ·
              refine ⟨8652187469576553360493121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5768124979717702240328747 8652187469576553360493121)
              ·
                refine ⟨6489140602182415020369841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8652187469576553360493121 6489140602182415020369841)
                ·
                  refine ⟨4866855451636811265277381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6489140602182415020369841 4866855451636811265277381)
                  ·
                    refine ⟨912535397181902112239509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4866855451636811265277381 912535397181902112239509)
                    ·
                      rfl

theorem cell23_5331469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_5331469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331469 prefixEnd_5331469 := by exact prefixLift 5331469
  have htrace : WordTrace (prefixWord ++ tailWord_5331469) baseStart_5331469 baseEnd_5331469 := by
    simpa [prefixWord, tailWord_5331469, baseEnd_5331469] using wordTrace_append hprefix tailTrace_5331469
  have hstable : (prefixWord ++ tailWord_5331469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331469).length < 2 ^ (prefixWord ++ tailWord_5331469).sum := by decide
  have hdescent : baseEnd_5331469 < baseStart_5331469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331491 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 2, 6]
def baseStart_5331491 : Nat := 118140960795 + 5331491 * 2 ^ 59
def prefixEnd_5331491 : Nat := 4983230072969 + 3 ^ 40 * 5331491 * 2
def baseEnd_5331491 : Nat := 912539162706701750214475

theorem tailTrace_5331491 : CollatzResearch.WordTrace tailWord_5331491 prefixEnd_5331491 912539162706701750214475 := by
  unfold tailWord_5331491
  simp only [CollatzResearch.WordTrace]
  refine ⟨194455451927926128015626327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129636967951950752010417551 194455451927926128015626327)
  ·
    refine ⟨291683177891889192023439491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194455451927926128015626327 291683177891889192023439491)
    ·
      refine ⟨437524766837833788035159237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291683177891889192023439491 437524766837833788035159237)
      ·
        refine ⟨82035893782093835256592357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 437524766837833788035159237 82035893782093835256592357)
        ·
          refine ⟨15381730084142594110611067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82035893782093835256592357 15381730084142594110611067)
          ·
            refine ⟨23072595126213891165916601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15381730084142594110611067 23072595126213891165916601)
            ·
              refine ⟨17304446344660418374437451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23072595126213891165916601 17304446344660418374437451)
              ·
                refine ⟨25956669516990627561656177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17304446344660418374437451 25956669516990627561656177)
                ·
                  refine ⟨19467502137742970671242133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25956669516990627561656177 19467502137742970671242133)
                  ·
                    refine ⟨912539162706701750214475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19467502137742970671242133 912539162706701750214475)
                    ·
                      rfl

theorem cell23_5331491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 6].length) (baseStart_5331491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331491 prefixEnd_5331491 := by exact prefixLift 5331491
  have htrace : WordTrace (prefixWord ++ tailWord_5331491) baseStart_5331491 baseEnd_5331491 := by
    simpa [prefixWord, tailWord_5331491, baseEnd_5331491] using wordTrace_append hprefix tailTrace_5331491
  have hstable : (prefixWord ++ tailWord_5331491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331491).length < 2 ^ (prefixWord ++ tailWord_5331491).sum := by decide
  have hdescent : baseEnd_5331491 < baseStart_5331491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331492 : List Nat := [2, 3, 1, 5, 1, 2, 1, 1, 1, 3, 3]
def baseStart_5331492 : Nat := 118140960795 + 5331492 * 2 ^ 59
def prefixEnd_5331492 : Nat := 4983230072969 + 3 ^ 40 * 5331492 * 2
def baseEnd_5331492 : Nat := 2737618001600759746730921

theorem tailTrace_5331492 : CollatzResearch.WordTrace tailWord_5331492 prefixEnd_5331492 2737618001600759746730921 := by
  unfold tailWord_5331492
  simp only [CollatzResearch.WordTrace]
  refine ⟨97227744200461252593206365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129636992267281670124275153 97227744200461252593206365)
  ·
    refine ⟨36460404075172969722452387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97227744200461252593206365 36460404075172969722452387)
    ·
      refine ⟨54690606112759454583678581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36460404075172969722452387 54690606112759454583678581)
      ·
        refine ⟨5127244323071198867219867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54690606112759454583678581 5127244323071198867219867)
        ·
          refine ⟨7690866484606798300829801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5127244323071198867219867 7690866484606798300829801)
          ·
            refine ⟨5768149863455098725622351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7690866484606798300829801 5768149863455098725622351)
            ·
              refine ⟨8652224795182648088433527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5768149863455098725622351 8652224795182648088433527)
              ·
                refine ⟨12978337192773972132650291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8652224795182648088433527 12978337192773972132650291)
                ·
                  refine ⟨19467505789160958198975437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12978337192773972132650291 19467505789160958198975437)
                  ·
                    refine ⟨7300314670935359324615789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19467505789160958198975437 7300314670935359324615789)
                    ·
                      refine ⟨2737618001600759746730921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7300314670935359324615789 2737618001600759746730921)
                      ·
                        rfl

theorem cell23_5331492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_5331492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331492 prefixEnd_5331492 := by exact prefixLift 5331492
  have htrace : WordTrace (prefixWord ++ tailWord_5331492) baseStart_5331492 baseEnd_5331492 := by
    simpa [prefixWord, tailWord_5331492, baseEnd_5331492] using wordTrace_append hprefix tailTrace_5331492
  have hstable : (prefixWord ++ tailWord_5331492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331492).length < 2 ^ (prefixWord ++ tailWord_5331492).sum := by decide
  have hdescent : baseEnd_5331492 < baseStart_5331492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331531 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 3]
def baseStart_5331531 : Nat := 118140960795 + 5331531 * 2 ^ 59
def prefixEnd_5331531 : Nat := 4983230072969 + 3 ^ 40 * 5331531 * 2
def baseEnd_5331531 : Nat := 2737638027346285094143241

theorem tailTrace_5331531 : CollatzResearch.WordTrace tailWord_5331531 prefixEnd_5331531 2737638027346285094143241 := by
  unfold tailWord_5331531
  simp only [CollatzResearch.WordTrace]
  refine ⟨194456910847781214847082447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129637940565187476564721631 194456910847781214847082447)
  ·
    refine ⟨291685366271671822270623671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194456910847781214847082447 291685366271671822270623671)
    ·
      refine ⟨437528049407507733405935507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291685366271671822270623671 437528049407507733405935507)
      ·
        refine ⟨656292074111261600108903261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437528049407507733405935507 656292074111261600108903261)
        ·
          refine ⟨246109527791723100040838723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 656292074111261600108903261 246109527791723100040838723)
          ·
            refine ⟨369164291687584650061258085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246109527791723100040838723 369164291687584650061258085)
            ·
              refine ⟨69218304691422121886485891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 369164291687584650061258085 69218304691422121886485891)
              ·
                refine ⟨103827457037133182829728837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69218304691422121886485891 103827457037133182829728837)
                ·
                  refine ⟨19467648194462471780574157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103827457037133182829728837 19467648194462471780574157)
                  ·
                    refine ⟨7300368072923426917715309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19467648194462471780574157 7300368072923426917715309)
                    ·
                      refine ⟨2737638027346285094143241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7300368072923426917715309 2737638027346285094143241)
                      ·
                        rfl

theorem cell23_5331531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 3].length) (baseStart_5331531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331531 prefixEnd_5331531 := by exact prefixLift 5331531
  have htrace : WordTrace (prefixWord ++ tailWord_5331531) baseStart_5331531 baseEnd_5331531 := by
    simpa [prefixWord, tailWord_5331531, baseEnd_5331531] using wordTrace_append hprefix tailTrace_5331531
  have hstable : (prefixWord ++ tailWord_5331531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331531).length < 2 ^ (prefixWord ++ tailWord_5331531).sum := by decide
  have hdescent : baseEnd_5331531 < baseStart_5331531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331591 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_5331591 : Nat := 118140960795 + 5331591 * 2 ^ 59
def prefixEnd_5331591 : Nat := 4983230072969 + 3 ^ 40 * 5331591 * 2
def baseEnd_5331591 : Nat := 2737668836185554859392965

theorem tailTrace_5331591 : CollatzResearch.WordTrace tailWord_5331591 prefixEnd_5331591 2737668836185554859392965 := by
  unfold tailWord_5331591
  simp only [CollatzResearch.WordTrace]
  refine ⟨194459099227563845094266627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129639399485042563396177751 194459099227563845094266627)
  ·
    refine ⟨291688648841345767641399941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194459099227563845094266627 291688648841345767641399941)
    ·
      refine ⟨54691621657752331432762489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 291688648841345767641399941 54691621657752331432762489)
      ·
        refine ⟨41018716243314248574571867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54691621657752331432762489 41018716243314248574571867)
        ·
          refine ⟨61528074364971372861857801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41018716243314248574571867 61528074364971372861857801)
          ·
            refine ⟨46146055773728529646393351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61528074364971372861857801 46146055773728529646393351)
            ·
              refine ⟨69219083660592794469590027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46146055773728529646393351 69219083660592794469590027)
              ·
                refine ⟨103828625490889191704385041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69219083660592794469590027 103828625490889191704385041)
                ·
                  refine ⟨77871469118166893778288781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103828625490889191704385041 77871469118166893778288781)
                  ·
                    refine ⟨29201800919312585166858293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77871469118166893778288781 29201800919312585166858293)
                    ·
                      refine ⟨2737668836185554859392965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29201800919312585166858293 2737668836185554859392965)
                      ·
                        rfl

theorem cell23_5331591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_5331591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331591 prefixEnd_5331591 := by exact prefixLift 5331591
  have htrace : WordTrace (prefixWord ++ tailWord_5331591) baseStart_5331591 baseEnd_5331591 := by
    simpa [prefixWord, tailWord_5331591, baseEnd_5331591] using wordTrace_append hprefix tailTrace_5331591
  have hstable : (prefixWord ++ tailWord_5331591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331591).length < 2 ^ (prefixWord ++ tailWord_5331591).sum := by decide
  have hdescent : baseEnd_5331591 < baseStart_5331591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331608 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 1, 4, 3]
def baseStart_5331608 : Nat := 118140960795 + 5331608 * 2 ^ 59
def prefixEnd_5331608 : Nat := 4983230072969 + 3 ^ 40 * 5331608 * 2
def baseEnd_5331608 : Nat := 2737677565356681292880387

theorem tailTrace_5331608 : CollatzResearch.WordTrace tailWord_5331608 prefixEnd_5331608 2737677565356681292880387 := by
  unfold tailWord_5331608
  simp only [CollatzResearch.WordTrace]
  refine ⟨97229859634251128498817739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129639812845668171331756985 97229859634251128498817739)
  ·
    refine ⟨145844789451376692748226609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97229859634251128498817739 145844789451376692748226609)
    ·
      refine ⟨109383592088532519561169957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145844789451376692748226609 109383592088532519561169957)
      ·
        refine ⟨20509423516599847417719367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109383592088532519561169957 20509423516599847417719367)
        ·
          refine ⟨30764135274899771126579051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20509423516599847417719367 30764135274899771126579051)
          ·
            refine ⟨46146202912349656689868577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30764135274899771126579051 46146202912349656689868577)
            ·
              refine ⟨34609652184262242517401433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46146202912349656689868577 34609652184262242517401433)
              ·
                refine ⟨25957239138196681888051075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34609652184262242517401433 25957239138196681888051075)
                ·
                  refine ⟨38935858707295022832076613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25957239138196681888051075 38935858707295022832076613)
                  ·
                    refine ⟨7300473507617816781014365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38935858707295022832076613 7300473507617816781014365)
                    ·
                      refine ⟨2737677565356681292880387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7300473507617816781014365 2737677565356681292880387)
                      ·
                        rfl

theorem cell23_5331608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_5331608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331608 prefixEnd_5331608 := by exact prefixLift 5331608
  have htrace : WordTrace (prefixWord ++ tailWord_5331608) baseStart_5331608 baseEnd_5331608 := by
    simpa [prefixWord, tailWord_5331608, baseEnd_5331608] using wordTrace_append hprefix tailTrace_5331608
  have hstable : (prefixWord ++ tailWord_5331608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331608).length < 2 ^ (prefixWord ++ tailWord_5331608).sum := by decide
  have hdescent : baseEnd_5331608 < baseStart_5331608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331645 : List Nat := [1, 4, 1, 2, 1, 5, 1, 2, 6]
def baseStart_5331645 : Nat := 118140960795 + 5331645 * 2 ^ 59
def prefixEnd_5331645 : Nat := 4983230072969 + 3 ^ 40 * 5331645 * 2
def baseEnd_5331645 : Nat := 304188507126766405346413

theorem tailTrace_5331645 : CollatzResearch.WordTrace tailWord_5331645 prefixEnd_5331645 304188507126766405346413 := by
  unfold tailWord_5331645
  simp only [CollatzResearch.WordTrace]
  refine ⟨194461068769368212316732389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129640712512912141544488259 194461068769368212316732389)
  ·
    refine ⟨36461450394256539809387323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194461068769368212316732389 36461450394256539809387323)
    ·
      refine ⟨54692175591384809714080985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36461450394256539809387323 54692175591384809714080985)
      ·
        refine ⟨41019131693538607285560739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54692175591384809714080985 41019131693538607285560739)
        ·
          refine ⟨61528697540307910928341109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41019131693538607285560739 61528697540307910928341109)
          ·
            refine ⟨5768315394403866649531979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61528697540307910928341109 5768315394403866649531979)
            ·
              refine ⟨8652473091605799974297969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5768315394403866649531979 8652473091605799974297969)
              ·
                refine ⟨6489354818704349980723477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8652473091605799974297969 6489354818704349980723477)
                ·
                  refine ⟨304188507126766405346413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6489354818704349980723477 304188507126766405346413)
                  ·
                    rfl

theorem cell23_5331645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_5331645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331645 prefixEnd_5331645 := by exact prefixLift 5331645
  have htrace : WordTrace (prefixWord ++ tailWord_5331645) baseStart_5331645 baseEnd_5331645 := by
    simpa [prefixWord, tailWord_5331645, baseEnd_5331645] using wordTrace_append hprefix tailTrace_5331645
  have hstable : (prefixWord ++ tailWord_5331645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331645).length < 2 ^ (prefixWord ++ tailWord_5331645).sum := by decide
  have hdescent : baseEnd_5331645 < baseStart_5331645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331649 : List Nat := [1, 2, 6, 2, 1, 1, 2, 1, 3, 4]
def baseStart_5331649 : Nat := 118140960795 + 5331649 * 2 ^ 59
def prefixEnd_5331649 : Nat := 4983230072969 + 3 ^ 40 * 5331649 * 2
def baseEnd_5331649 : Nat := 912566206021171877489233

theorem tailTrace_5331649 : CollatzResearch.WordTrace tailWord_5331649 prefixEnd_5331649 912566206021171877489233 := by
  unfold tailWord_5331649
  simp only [CollatzResearch.WordTrace]
  refine ⟨194461214661353720999878001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129640809774235813999918667 194461214661353720999878001)
  ·
    refine ⟨145845910996015290749908501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194461214661353720999878001 145845910996015290749908501)
    ·
      refine ⟨6836527077938216753901961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 145845910996015290749908501 6836527077938216753901961)
      ·
        refine ⟨5127395308453662565426471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6836527077938216753901961 5127395308453662565426471)
        ·
          refine ⟨7691092962680493848139707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5127395308453662565426471 7691092962680493848139707)
          ·
            refine ⟨11536639444020740772209561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7691092962680493848139707 11536639444020740772209561)
            ·
              refine ⟨8652479583015555579157171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11536639444020740772209561 8652479583015555579157171)
              ·
                refine ⟨12978719374523333368735757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8652479583015555579157171 12978719374523333368735757)
                ·
                  refine ⟨4867019765446250013275909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12978719374523333368735757 4867019765446250013275909)
                  ·
                    refine ⟨912566206021171877489233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4867019765446250013275909 912566206021171877489233)
                    ·
                      rfl

theorem cell23_5331649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_5331649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331649 prefixEnd_5331649 := by exact prefixLift 5331649
  have htrace : WordTrace (prefixWord ++ tailWord_5331649) baseStart_5331649 baseEnd_5331649 := by
    simpa [prefixWord, tailWord_5331649, baseEnd_5331649] using wordTrace_append hprefix tailTrace_5331649
  have hstable : (prefixWord ++ tailWord_5331649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331649).length < 2 ^ (prefixWord ++ tailWord_5331649).sum := by decide
  have hdescent : baseEnd_5331649 < baseStart_5331649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331695 : List Nat := [1, 1, 2, 1, 5, 2, 2, 3, 1, 1, 4]
def baseStart_5331695 : Nat := 118140960795 + 5331695 * 2 ^ 59
def prefixEnd_5331695 : Nat := 4983230072969 + 3 ^ 40 * 5331695 * 2
def baseEnd_5331695 : Nat := 2737722238173622452492487

theorem tailTrace_5331695 : CollatzResearch.WordTrace tailWord_5331695 prefixEnd_5331695 2737722238173622452492487 := by
  unfold tailWord_5331695
  simp only [CollatzResearch.WordTrace]
  refine ⟨194462892419187070856052539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129641928279458047237368359 194462892419187070856052539)
  ·
    refine ⟨291694338628780606284078809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194462892419187070856052539 291694338628780606284078809)
    ·
      refine ⟨218770753971585454713059107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291694338628780606284078809 218770753971585454713059107)
      ·
        refine ⟨328156130957378182069588661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218770753971585454713059107 328156130957378182069588661)
        ·
          refine ⟨30764637277254204569023937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 328156130957378182069588661 30764637277254204569023937)
          ·
            refine ⟨23073477957940653426767953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30764637277254204569023937 23073477957940653426767953)
            ·
              refine ⟨17305108468455490070075965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23073477957940653426767953 17305108468455490070075965)
              ·
                refine ⟨6489415675670808776278487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17305108468455490070075965 6489415675670808776278487)
                ·
                  refine ⟨9734123513506213164417731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6489415675670808776278487 9734123513506213164417731)
                  ·
                    refine ⟨14601185270259319746626597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9734123513506213164417731 14601185270259319746626597)
                    ·
                      refine ⟨2737722238173622452492487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14601185270259319746626597 2737722238173622452492487)
                      ·
                        rfl

theorem cell23_5331695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 1, 4].length) (baseStart_5331695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331695 prefixEnd_5331695 := by exact prefixLift 5331695
  have htrace : WordTrace (prefixWord ++ tailWord_5331695) baseStart_5331695 baseEnd_5331695 := by
    simpa [prefixWord, tailWord_5331695, baseEnd_5331695] using wordTrace_append hprefix tailTrace_5331695
  have hstable : (prefixWord ++ tailWord_5331695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331695).length < 2 ^ (prefixWord ++ tailWord_5331695).sum := by decide
  have hdescent : baseEnd_5331695 < baseStart_5331695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331708 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_5331708 : Nat := 118140960795 + 5331708 * 2 ^ 59
def prefixEnd_5331708 : Nat := 4983230072969 + 3 ^ 40 * 5331708 * 2
def baseEnd_5331708 : Nat := 2737728913422130901629927

theorem tailTrace_5331708 : CollatzResearch.WordTrace tailWord_5331708 prefixEnd_5331708 2737728913422130901629927 := by
  unfold tailWord_5331708
  simp only [CollatzResearch.WordTrace]
  refine ⟨97231683284069987038137889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129642244378759982717517185 97231683284069987038137889)
  ·
    refine ⟨72923762463052490278603417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97231683284069987038137889 72923762463052490278603417)
    ·
      refine ⟨54692821847289367708952563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72923762463052490278603417 54692821847289367708952563)
      ·
        refine ⟨82039232770934051563428845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54692821847289367708952563 82039232770934051563428845)
        ·
          refine ⟨30764712289100269336285817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82039232770934051563428845 30764712289100269336285817)
          ·
            refine ⟨23073534216825202002214363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30764712289100269336285817 23073534216825202002214363)
            ·
              refine ⟨34610301325237803003321545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23073534216825202002214363 34610301325237803003321545)
              ·
                refine ⟨25957725993928352252491159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34610301325237803003321545 25957725993928352252491159)
                ·
                  refine ⟨38936588990892528378736739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25957725993928352252491159 38936588990892528378736739)
                  ·
                    refine ⟨58404883486338792568105109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38936588990892528378736739 58404883486338792568105109)
                    ·
                      refine ⟨2737728913422130901629927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58404883486338792568105109 2737728913422130901629927)
                      ·
                        rfl

theorem cell23_5331708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_5331708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331708 prefixEnd_5331708 := by exact prefixLift 5331708
  have htrace : WordTrace (prefixWord ++ tailWord_5331708) baseStart_5331708 baseEnd_5331708 := by
    simpa [prefixWord, tailWord_5331708, baseEnd_5331708] using wordTrace_append hprefix tailTrace_5331708
  have hstable : (prefixWord ++ tailWord_5331708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331708).length < 2 ^ (prefixWord ++ tailWord_5331708).sum := by decide
  have hdescent : baseEnd_5331708 < baseStart_5331708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331745 : List Nat := [1, 2, 3, 2, 1, 2, 3, 2, 1, 3, 3]
def baseStart_5331745 : Nat := 118140960795 + 5331745 * 2 ^ 59
def prefixEnd_5331745 : Nat := 4983230072969 + 3 ^ 40 * 5331745 * 2
def baseEnd_5331745 : Nat := 2737747912206347256867257

theorem tailTrace_5331745 : CollatzResearch.WordTrace tailWord_5331745 prefixEnd_5331745 2737747912206347256867257 := by
  unfold tailWord_5331745
  simp only [CollatzResearch.WordTrace]
  refine ⟨194464716069005929395372689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129643144046003952930248459 194464716069005929395372689)
  ·
    refine ⟨145848537051754447046529517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194464716069005929395372689 145848537051754447046529517)
    ·
      refine ⟨54693201394407917642448569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145848537051754447046529517 54693201394407917642448569)
      ·
        refine ⟨41019901045805938231836427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54693201394407917642448569 41019901045805938231836427)
        ·
          refine ⟨61529851568708907347754641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41019901045805938231836427 61529851568708907347754641)
          ·
            refine ⟨46147388676531680510815981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61529851568708907347754641 46147388676531680510815981)
            ·
              refine ⟨17305270753699380191555993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46147388676531680510815981 17305270753699380191555993)
              ·
                refine ⟨12978953065274535143666995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17305270753699380191555993 12978953065274535143666995)
                ·
                  refine ⟨19468429597911802715500493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12978953065274535143666995 19468429597911802715500493)
                  ·
                    refine ⟨7300661099216926018312685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19468429597911802715500493 7300661099216926018312685)
                    ·
                      refine ⟨2737747912206347256867257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7300661099216926018312685 2737747912206347256867257)
                      ·
                        rfl

theorem cell23_5331745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_5331745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331745 prefixEnd_5331745 := by exact prefixLift 5331745
  have htrace : WordTrace (prefixWord ++ tailWord_5331745) baseStart_5331745 baseEnd_5331745 := by
    simpa [prefixWord, tailWord_5331745, baseEnd_5331745] using wordTrace_append hprefix tailTrace_5331745
  have hstable : (prefixWord ++ tailWord_5331745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331745).length < 2 ^ (prefixWord ++ tailWord_5331745).sum := by decide
  have hdescent : baseEnd_5331745 < baseStart_5331745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331755 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 5, 3, 2]
def baseStart_5331755 : Nat := 118140960795 + 5331755 * 2 ^ 59
def prefixEnd_5331755 : Nat := 4983230072969 + 3 ^ 40 * 5331755 * 2
def baseEnd_5331755 : Nat := 2737753047012892217742211

theorem tailTrace_5331755 : CollatzResearch.WordTrace tailWord_5331755 prefixEnd_5331755 2737753047012892217742211 := by
  unfold tailWord_5331755
  simp only [CollatzResearch.WordTrace]
  refine ⟨194465080798969701103236719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129643387199313134068824479 194465080798969701103236719)
  ·
    refine ⟨291697621198454551654855079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194465080798969701103236719 291697621198454551654855079)
    ·
      refine ⟨437546431797681827482282619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291697621198454551654855079 437546431797681827482282619)
      ·
        refine ⟨656319647696522741223423929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437546431797681827482282619 656319647696522741223423929)
        ·
          refine ⟨492239735772392055917567947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 656319647696522741223423929 492239735772392055917567947)
          ·
            refine ⟨738359603658588083876351921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492239735772392055917567947 738359603658588083876351921)
            ·
              refine ⟨553769702743941062907263941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738359603658588083876351921 553769702743941062907263941)
              ·
                refine ⟨103831819264488949295111989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 553769702743941062907263941 103831819264488949295111989)
                ·
                  refine ⟨9734233056045838996416749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103831819264488949295111989 9734233056045838996416749)
                  ·
                    refine ⟨3650337396017189623656281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9734233056045838996416749 3650337396017189623656281)
                    ·
                      refine ⟨2737753047012892217742211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3650337396017189623656281 2737753047012892217742211)
                      ·
                        rfl

theorem cell23_5331755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 3, 2].length) (baseStart_5331755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331755 prefixEnd_5331755 := by exact prefixLift 5331755
  have htrace : WordTrace (prefixWord ++ tailWord_5331755) baseStart_5331755 baseEnd_5331755 := by
    simpa [prefixWord, tailWord_5331755, baseEnd_5331755] using wordTrace_append hprefix tailTrace_5331755
  have hstable : (prefixWord ++ tailWord_5331755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331755).length < 2 ^ (prefixWord ++ tailWord_5331755).sum := by decide
  have hdescent : baseEnd_5331755 < baseStart_5331755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331757 : List Nat := [1, 5, 3, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_5331757 : Nat := 118140960795 + 5331757 * 2 ^ 59
def prefixEnd_5331757 : Nat := 4983230072969 + 3 ^ 40 * 5331757 * 2
def baseEnd_5331757 : Nat := 2737754073974201209917203

theorem tailTrace_5331757 : CollatzResearch.WordTrace tailWord_5331757 prefixEnd_5331757 2737754073974201209917203 := by
  unfold tailWord_5331757
  simp only [CollatzResearch.WordTrace]
  refine ⟨194465153744962455444809525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129643435829974970296539683 194465153744962455444809525)
  ·
    refine ⟨18231108163590230197950893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194465153744962455444809525 18231108163590230197950893)
    ·
      refine ⟨6836665561346336324231585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18231108163590230197950893 6836665561346336324231585)
      ·
        refine ⟨5127499171009752243173689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6836665561346336324231585 5127499171009752243173689)
        ·
          refine ⟨3845624378257314182380267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5127499171009752243173689 3845624378257314182380267)
          ·
            refine ⟨5768436567385971273570401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3845624378257314182380267 5768436567385971273570401)
            ·
              refine ⟨4326327425539478455177801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5768436567385971273570401 4326327425539478455177801)
              ·
                refine ⟨3244745569154608841383351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4326327425539478455177801 3244745569154608841383351)
                ·
                  refine ⟨4867118353731913262075027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3244745569154608841383351 4867118353731913262075027)
                  ·
                    refine ⟨7300677530597869893112541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4867118353731913262075027 7300677530597869893112541)
                    ·
                      refine ⟨2737754073974201209917203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7300677530597869893112541 2737754073974201209917203)
                      ·
                        rfl

theorem cell23_5331757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_5331757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331757 prefixEnd_5331757 := by exact prefixLift 5331757
  have htrace : WordTrace (prefixWord ++ tailWord_5331757) baseStart_5331757 baseEnd_5331757 := by
    simpa [prefixWord, tailWord_5331757, baseEnd_5331757] using wordTrace_append hprefix tailTrace_5331757
  have hstable : (prefixWord ++ tailWord_5331757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331757).length < 2 ^ (prefixWord ++ tailWord_5331757).sum := by decide
  have hdescent : baseEnd_5331757 < baseStart_5331757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331763 : List Nat := [1, 1, 1, 2, 6, 3, 2, 2, 1, 2, 2]
def baseStart_5331763 : Nat := 118140960795 + 5331763 * 2 ^ 59
def prefixEnd_5331763 : Nat := 4983230072969 + 3 ^ 40 * 5331763 * 2
def baseEnd_5331763 : Nat := 2737757154858128186442175

theorem tailTrace_5331763 : CollatzResearch.WordTrace tailWord_5331763 prefixEnd_5331763 2737757154858128186442175 := by
  unfold tailWord_5331763
  simp only [CollatzResearch.WordTrace]
  refine ⟨194465372582940718469527943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129643581721960478979685295 194465372582940718469527943)
  ·
    refine ⟨291698058874411077704291915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194465372582940718469527943 291698058874411077704291915)
    ·
      refine ⟨437547088311616616556437873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291698058874411077704291915 437547088311616616556437873)
      ·
        refine ⟨328160316233712462417328405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437547088311616616556437873 328160316233712462417328405)
        ·
          refine ⟨15382514823455271675812269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 328160316233712462417328405 15382514823455271675812269)
          ·
            refine ⟨5768443058795726878429601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15382514823455271675812269 5768443058795726878429601)
            ·
              refine ⟨4326332294096795158822201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5768443058795726878429601 4326332294096795158822201)
              ·
                refine ⟨3244749220572596369116651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4326332294096795158822201 3244749220572596369116651)
                ·
                  refine ⟨4867123830858894553674977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3244749220572596369116651 4867123830858894553674977)
                  ·
                    refine ⟨3650342873144170915256233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4867123830858894553674977 3650342873144170915256233)
                    ·
                      refine ⟨2737757154858128186442175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3650342873144170915256233 2737757154858128186442175)
                      ·
                        rfl

theorem cell23_5331763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 1, 2, 2].length) (baseStart_5331763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331763 prefixEnd_5331763 := by exact prefixLift 5331763
  have htrace : WordTrace (prefixWord ++ tailWord_5331763) baseStart_5331763 baseEnd_5331763 := by
    simpa [prefixWord, tailWord_5331763, baseEnd_5331763] using wordTrace_append hprefix tailTrace_5331763
  have hstable : (prefixWord ++ tailWord_5331763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331763).length < 2 ^ (prefixWord ++ tailWord_5331763).sum := by decide
  have hdescent : baseEnd_5331763 < baseStart_5331763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331768 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 1, 5, 4]
def baseStart_5331768 : Nat := 118140960795 + 5331768 * 2 ^ 59
def prefixEnd_5331768 : Nat := 4983230072969 + 3 ^ 40 * 5331768 * 2
def baseEnd_5331768 : Nat := 2737759722261400666879651

theorem tailTrace_5331768 : CollatzResearch.WordTrace tailWord_5331768 prefixEnd_5331768 2737759722261400666879651 := by
  unfold tailWord_5331768
  simp only [CollatzResearch.WordTrace]
  refine ⟨97232777473961302161729979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129643703298615069548973305 97232777473961302161729979)
  ·
    refine ⟨145849166210941953242594969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97232777473961302161729979 145849166210941953242594969)
    ·
      refine ⟨109386874658206464931946227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145849166210941953242594969 109386874658206464931946227)
      ·
        refine ⟨164080311987309697397919341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109386874658206464931946227 164080311987309697397919341)
        ·
          refine ⟨61530116995241136524219753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164080311987309697397919341 61530116995241136524219753)
          ·
            refine ⟨46147587746430852393164815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61530116995241136524219753 46147587746430852393164815)
            ·
              refine ⟨69221381619646278589747223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46147587746430852393164815 69221381619646278589747223)
              ·
                refine ⟨103832072429469417884620835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69221381619646278589747223 103832072429469417884620835)
                ·
                  refine ⟨155748108644204126826931253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103832072429469417884620835 155748108644204126826931253)
                  ·
                    refine ⟨14601385185394136890024805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 155748108644204126826931253 14601385185394136890024805)
                    ·
                      refine ⟨2737759722261400666879651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14601385185394136890024805 2737759722261400666879651)
                      ·
                        rfl

theorem cell23_5331768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_5331768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331768 prefixEnd_5331768 := by exact prefixLift 5331768
  have htrace : WordTrace (prefixWord ++ tailWord_5331768) baseStart_5331768 baseEnd_5331768 := by
    simpa [prefixWord, tailWord_5331768, baseEnd_5331768] using wordTrace_append hprefix tailTrace_5331768
  have hstable : (prefixWord ++ tailWord_5331768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331768).length < 2 ^ (prefixWord ++ tailWord_5331768).sum := by decide
  have hdescent : baseEnd_5331768 < baseStart_5331768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331802 : List Nat := [3, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2]
def baseStart_5331802 : Nat := 118140960795 + 5331802 * 2 ^ 59
def prefixEnd_5331802 : Nat := 4983230072969 + 3 ^ 40 * 5331802 * 2
def baseEnd_5331802 : Nat := 2737777180603653533854495

theorem tailTrace_5331802 : CollatzResearch.WordTrace tailWord_5331802 prefixEnd_5331802 2737777180603653533854495 := by
  unfold tailWord_5331802
  simp only [CollatzResearch.WordTrace]
  refine ⟨48616698757449857032549415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129644530019866285420131773 48616698757449857032549415)
  ·
    refine ⟨72925048136174785548824123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48616698757449857032549415 72925048136174785548824123)
    ·
      refine ⟨109387572204262178323236185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72925048136174785548824123 109387572204262178323236185)
      ·
        refine ⟨82040679153196633742427139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109387572204262178323236185 82040679153196633742427139)
        ·
          refine ⟨123061018729794950613640709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82040679153196633742427139 123061018729794950613640709)
          ·
            refine ⟨23073941011836553240057633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123061018729794950613640709 23073941011836553240057633)
            ·
              refine ⟨17305455758877414930043225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23073941011836553240057633 17305455758877414930043225)
              ·
                refine ⟨12979091819158061197532419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17305455758877414930043225 12979091819158061197532419)
                ·
                  refine ⟨19468637728737091796298629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12979091819158061197532419 19468637728737091796298629)
                  ·
                    refine ⟨3650369574138204711805993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19468637728737091796298629 3650369574138204711805993)
                    ·
                      refine ⟨2737777180603653533854495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3650369574138204711805993 2737777180603653533854495)
                      ·
                        rfl

theorem cell23_5331802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_5331802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331802 prefixEnd_5331802 := by exact prefixLift 5331802
  have htrace : WordTrace (prefixWord ++ tailWord_5331802) baseStart_5331802 baseEnd_5331802 := by
    simpa [prefixWord, tailWord_5331802, baseEnd_5331802] using wordTrace_append hprefix tailTrace_5331802
  have hstable : (prefixWord ++ tailWord_5331802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331802).length < 2 ^ (prefixWord ++ tailWord_5331802).sum := by decide
  have hdescent : baseEnd_5331802 < baseStart_5331802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331808 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 9]
def baseStart_5331808 : Nat := 118140960795 + 5331808 * 2 ^ 59
def prefixEnd_5331808 : Nat := 4983230072969 + 3 ^ 40 * 5331808 * 2
def baseEnd_5331808 : Nat := 304197806831953390042163

theorem tailTrace_5331808 : CollatzResearch.WordTrace tailWord_5331808 prefixEnd_5331808 304197806831953390042163 := by
  unfold tailWord_5331808
  simp only [CollatzResearch.WordTrace]
  refine ⟨97233506933888845577458039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129644675911851794103277385 97233506933888845577458039)
  ·
    refine ⟨145850260400833268366187059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97233506933888845577458039 145850260400833268366187059)
    ·
      refine ⟨218775390601249902549280589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145850260400833268366187059 218775390601249902549280589)
      ·
        refine ⟨82040771475468713455980221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218775390601249902549280589 82040771475468713455980221)
        ·
          refine ⟨30765289303300767545992583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82040771475468713455980221 30765289303300767545992583)
          ·
            refine ⟨46147933954951151318988875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30765289303300767545992583 46147933954951151318988875)
            ·
              refine ⟨69221900932426726978483313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46147933954951151318988875 69221900932426726978483313)
              ·
                refine ⟨51916425699320045233862485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69221900932426726978483313 51916425699320045233862485)
                ·
                  refine ⟨304197806831953390042163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51916425699320045233862485 304197806831953390042163)
                  ·
                    rfl

theorem cell23_5331808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 9].length) (baseStart_5331808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331808 prefixEnd_5331808 := by exact prefixLift 5331808
  have htrace : WordTrace (prefixWord ++ tailWord_5331808) baseStart_5331808 baseEnd_5331808 := by
    simpa [prefixWord, tailWord_5331808, baseEnd_5331808] using wordTrace_append hprefix tailTrace_5331808
  have hstable : (prefixWord ++ tailWord_5331808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331808).length < 2 ^ (prefixWord ++ tailWord_5331808).sum := by decide
  have hdescent : baseEnd_5331808 < baseStart_5331808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331815 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_5331815 : Nat := 118140960795 + 5331815 * 2 ^ 59
def prefixEnd_5331815 : Nat := 4983230072969 + 3 ^ 40 * 5331815 * 2
def baseEnd_5331815 : Nat := 2737783855852161982991935

theorem tailTrace_5331815 : CollatzResearch.WordTrace tailWord_5331815 prefixEnd_5331815 2737783855852161982991935 := by
  unfold tailWord_5331815
  simp only [CollatzResearch.WordTrace]
  refine ⟨194467269178752331350420899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129644846119168220900280599 194467269178752331350420899)
  ·
    refine ⟨291700903768128497025631349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194467269178752331350420899 291700903768128497025631349)
    ·
      refine ⟨27346959728262046596152939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 291700903768128497025631349 27346959728262046596152939)
      ·
        refine ⟨41020439592393069894229409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27346959728262046596152939 41020439592393069894229409)
        ·
          refine ⟨30765329694294802420672057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41020439592393069894229409 30765329694294802420672057)
          ·
            refine ⟨23073997270721101815504043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30765329694294802420672057 23073997270721101815504043)
            ·
              refine ⟨34610995906081652723256065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23073997270721101815504043 34610995906081652723256065)
              ·
                refine ⟨25958246929561239542442049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34610995906081652723256065 25958246929561239542442049)
                ·
                  refine ⟨19468685197170929656831537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25958246929561239542442049 19468685197170929656831537)
                  ·
                    refine ⟨14601513897878197242623653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19468685197170929656831537 14601513897878197242623653)
                    ·
                      refine ⟨2737783855852161982991935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14601513897878197242623653 2737783855852161982991935)
                      ·
                        rfl

theorem cell23_5331815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_5331815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331815 prefixEnd_5331815 := by exact prefixLift 5331815
  have htrace : WordTrace (prefixWord ++ tailWord_5331815) baseStart_5331815 baseEnd_5331815 := by
    simpa [prefixWord, tailWord_5331815, baseEnd_5331815] using wordTrace_append hprefix tailTrace_5331815
  have hstable : (prefixWord ++ tailWord_5331815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331815).length < 2 ^ (prefixWord ++ tailWord_5331815).sum := by decide
  have hdescent : baseEnd_5331815 < baseStart_5331815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331819 : List Nat := [1, 1, 1, 1, 2, 2, 7, 2, 2, 2, 2]
def baseStart_5331819 : Nat := 118140960795 + 5331819 * 2 ^ 59
def prefixEnd_5331819 : Nat := 4983230072969 + 3 ^ 40 * 5331819 * 2
def baseEnd_5331819 : Nat := 2737785909774779967341917

theorem tailTrace_5331819 : CollatzResearch.WordTrace tailWord_5331819 prefixEnd_5331819 2737785909774779967341917 := by
  unfold tailWord_5331819
  simp only [CollatzResearch.WordTrace]
  refine ⟨194467415070737840033566511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129644943380491893355711007 194467415070737840033566511)
  ·
    refine ⟨291701122606106760050349767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194467415070737840033566511 291701122606106760050349767)
    ·
      refine ⟨437551683909160140075524651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291701122606106760050349767 437551683909160140075524651)
      ·
        refine ⟨656327525863740210113286977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437551683909160140075524651 656327525863740210113286977)
        ·
          refine ⟨492245644397805157584965233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 656327525863740210113286977 492245644397805157584965233)
          ·
            refine ⟨369184233298353868188723925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 492245644397805157584965233 369184233298353868188723925)
            ·
              refine ⟨8652755467930168785673217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 369184233298353868188723925 8652755467930168785673217)
              ·
                refine ⟨6489566600947626589254913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8652755467930168785673217 6489566600947626589254913)
                ·
                  refine ⟨4867174950710719941941185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6489566600947626589254913 4867174950710719941941185)
                  ·
                    refine ⟨3650381213033039956455889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4867174950710719941941185 3650381213033039956455889)
                    ·
                      refine ⟨2737785909774779967341917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3650381213033039956455889 2737785909774779967341917)
                      ·
                        rfl

theorem cell23_5331819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 2, 2].length) (baseStart_5331819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331819 prefixEnd_5331819 := by exact prefixLift 5331819
  have htrace : WordTrace (prefixWord ++ tailWord_5331819) baseStart_5331819 baseEnd_5331819 := by
    simpa [prefixWord, tailWord_5331819, baseEnd_5331819] using wordTrace_append hprefix tailTrace_5331819
  have hstable : (prefixWord ++ tailWord_5331819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331819).length < 2 ^ (prefixWord ++ tailWord_5331819).sum := by decide
  have hdescent : baseEnd_5331819 < baseStart_5331819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331825 : List Nat := [1, 2, 2, 2, 1, 5, 2, 1, 7]
def baseStart_5331825 : Nat := 118140960795 + 5331825 * 2 ^ 59
def prefixEnd_5331825 : Nat := 4983230072969 + 3 ^ 40 * 5331825 * 2
def baseEnd_5331825 : Nat := 304198776739856327096321

theorem tailTrace_5331825 : CollatzResearch.WordTrace tailWord_5331825 prefixEnd_5331825 304198776739856327096321 := by
  unfold tailWord_5331825
  simp only [CollatzResearch.WordTrace]
  refine ⟨194467633908716103058284929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129645089272477402038856619 194467633908716103058284929)
  ·
    refine ⟨145850725431537077293713697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194467633908716103058284929 145850725431537077293713697)
    ·
      refine ⟨109388044073652807970285273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145850725431537077293713697 109388044073652807970285273)
      ·
        refine ⟨82041033055239605977713955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109388044073652807970285273 82041033055239605977713955)
        ·
          refine ⟨123061549582859408966570933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82041033055239605977713955 123061549582859408966570933)
          ·
            refine ⟨11537020273393069590616025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123061549582859408966570933 11537020273393069590616025)
            ·
              refine ⟨8652765205044802192962019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11537020273393069590616025 8652765205044802192962019)
              ·
                refine ⟨12979147807567203289443029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8652765205044802192962019 12979147807567203289443029)
                ·
                  refine ⟨304198776739856327096321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12979147807567203289443029 304198776739856327096321)
                  ·
                    rfl

theorem cell23_5331825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 7].length) (baseStart_5331825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331825 prefixEnd_5331825 := by exact prefixLift 5331825
  have htrace : WordTrace (prefixWord ++ tailWord_5331825) baseStart_5331825 baseEnd_5331825 := by
    simpa [prefixWord, tailWord_5331825, baseEnd_5331825] using wordTrace_append hprefix tailTrace_5331825
  have hstable : (prefixWord ++ tailWord_5331825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331825).length < 2 ^ (prefixWord ++ tailWord_5331825).sum := by decide
  have hdescent : baseEnd_5331825 < baseStart_5331825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331835 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 3]
def baseStart_5331835 : Nat := 118140960795 + 5331835 * 2 ^ 59
def prefixEnd_5331835 : Nat := 4983230072969 + 3 ^ 40 * 5331835 * 2
def baseEnd_5331835 : Nat := 2737794125465251904741843

theorem tailTrace_5331835 : CollatzResearch.WordTrace tailWord_5331835 prefixEnd_5331835 2737794125465251904741843 := by
  unfold tailWord_5331835
  simp only [CollatzResearch.WordTrace]
  refine ⟨194467998638679874766148959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129645332425786583177432639 194467998638679874766148959)
  ·
    refine ⟨291701997958019812149223439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194467998638679874766148959 291701997958019812149223439)
    ·
      refine ⟨437552996937029718223835159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291701997958019812149223439 437552996937029718223835159)
      ·
        refine ⟨656329495405544577335752739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437552996937029718223835159 656329495405544577335752739)
        ·
          refine ⟨984494243108316866003629109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656329495405544577335752739 984494243108316866003629109)
          ·
            refine ⟨92296335291404706187840229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 984494243108316866003629109 92296335291404706187840229)
            ·
              refine ⟨17305562867138382410220043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92296335291404706187840229 17305562867138382410220043)
              ·
                refine ⟨25958344300707573615330065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17305562867138382410220043 25958344300707573615330065)
                ·
                  refine ⟨19468758225530680211497549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25958344300707573615330065 19468758225530680211497549)
                  ·
                    refine ⟨7300784334574005079311581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19468758225530680211497549 7300784334574005079311581)
                    ·
                      refine ⟨2737794125465251904741843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7300784334574005079311581 2737794125465251904741843)
                      ·
                        rfl

theorem cell23_5331835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 3].length) (baseStart_5331835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331835 prefixEnd_5331835 := by exact prefixLift 5331835
  have htrace : WordTrace (prefixWord ++ tailWord_5331835) baseStart_5331835 baseEnd_5331835 := by
    simpa [prefixWord, tailWord_5331835, baseEnd_5331835] using wordTrace_append hprefix tailTrace_5331835
  have hstable : (prefixWord ++ tailWord_5331835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331835).length < 2 ^ (prefixWord ++ tailWord_5331835).sum := by decide
  have hdescent : baseEnd_5331835 < baseStart_5331835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331875 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 4]
def baseStart_5331875 : Nat := 118140960795 + 5331875 * 2 ^ 59
def prefixEnd_5331875 : Nat := 4983230072969 + 3 ^ 40 * 5331875 * 2
def baseEnd_5331875 : Nat := 2737814664691431748241659

theorem tailTrace_5331875 : CollatzResearch.WordTrace tailWord_5331875 prefixEnd_5331875 2737814664691431748241659 := by
  unfold tailWord_5331875
  simp only [CollatzResearch.WordTrace]
  refine ⟨194469457558534961597605079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129646305039023307731736719 194469457558534961597605079)
  ·
    refine ⟨291704186337802442396407619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194469457558534961597605079 291704186337802442396407619)
    ·
      refine ⟨437556279506703663594611429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291704186337802442396407619 437556279506703663594611429)
      ·
        refine ⟨82041802407506936923989643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 437556279506703663594611429 82041802407506936923989643)
        ·
          refine ⟨123062703611260405385984465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82041802407506936923989643 123062703611260405385984465)
          ·
            refine ⟨92297027708445304039488349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123062703611260405385984465 92297027708445304039488349)
            ·
              refine ⟨34611385390666989014808131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92297027708445304039488349 34611385390666989014808131)
              ·
                refine ⟨51917078086000483522212197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34611385390666989014808131 51917078086000483522212197)
                ·
                  refine ⟨9734452141125090660414787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51917078086000483522212197 9734452141125090660414787)
                  ·
                    refine ⟨14601678211687635990622181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9734452141125090660414787 14601678211687635990622181)
                    ·
                      refine ⟨2737814664691431748241659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14601678211687635990622181 2737814664691431748241659)
                      ·
                        rfl

theorem cell23_5331875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_5331875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331875 prefixEnd_5331875 := by exact prefixLift 5331875
  have htrace : WordTrace (prefixWord ++ tailWord_5331875) baseStart_5331875 baseEnd_5331875 := by
    simpa [prefixWord, tailWord_5331875, baseEnd_5331875] using wordTrace_append hprefix tailTrace_5331875
  have hstable : (prefixWord ++ tailWord_5331875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331875).length < 2 ^ (prefixWord ++ tailWord_5331875).sum := by decide
  have hdescent : baseEnd_5331875 < baseStart_5331875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331895 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 3]
def baseStart_5331895 : Nat := 118140960795 + 5331895 * 2 ^ 59
def prefixEnd_5331895 : Nat := 4983230072969 + 3 ^ 40 * 5331895 * 2
def baseEnd_5331895 : Nat := 2737824934304521669991567

theorem tailTrace_5331895 : CollatzResearch.WordTrace tailWord_5331895 prefixEnd_5331895 2737824934304521669991567 := by
  unfold tailWord_5331895
  simp only [CollatzResearch.WordTrace]
  refine ⟨194470187018462505013333139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129646791345641670008888759 194470187018462505013333139)
  ·
    refine ⟨291705280527693757519999709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194470187018462505013333139 291705280527693757519999709)
    ·
      refine ⟨109389480197885159069999891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291705280527693757519999709 109389480197885159069999891)
      ·
        refine ⟨164084220296827738604999837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109389480197885159069999891 164084220296827738604999837)
        ·
          refine ⟨61531582611310401976874939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164084220296827738604999837 61531582611310401976874939)
          ·
            refine ⟨92297373916965602965312409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61531582611310401976874939 92297373916965602965312409)
            ·
              refine ⟨69223030437724202223984307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92297373916965602965312409 69223030437724202223984307)
              ·
                refine ⟨103834545656586303335976461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69223030437724202223984307 103834545656586303335976461)
                ·
                  refine ⟨38937954621219863750991173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103834545656586303335976461 38937954621219863750991173)
                  ·
                    refine ⟨7300866491478724453310845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38937954621219863750991173 7300866491478724453310845)
                    ·
                      refine ⟨2737824934304521669991567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7300866491478724453310845 2737824934304521669991567)
                      ·
                        rfl

theorem cell23_5331895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_5331895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331895 prefixEnd_5331895 := by exact prefixLift 5331895
  have htrace : WordTrace (prefixWord ++ tailWord_5331895) baseStart_5331895 baseEnd_5331895 := by
    simpa [prefixWord, tailWord_5331895, baseEnd_5331895] using wordTrace_append hprefix tailTrace_5331895
  have hstable : (prefixWord ++ tailWord_5331895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331895).length < 2 ^ (prefixWord ++ tailWord_5331895).sum := by decide
  have hdescent : baseEnd_5331895 < baseStart_5331895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331902 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_5331902 : Nat := 118140960795 + 5331902 * 2 ^ 59
def prefixEnd_5331902 : Nat := 4983230072969 + 3 ^ 40 * 5331902 * 2
def baseEnd_5331902 : Nat := 912609509556367714201345

theorem tailTrace_5331902 : CollatzResearch.WordTrace tailWord_5331902 prefixEnd_5331902 912609509556367714201345 := by
  unfold tailWord_5331902
  simp only [CollatzResearch.WordTrace]
  refine ⟨24308805291179643151104745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129646961552958096805891973 24308805291179643151104745)
  ·
    refine ⟨18231603968384732363328559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24308805291179643151104745 18231603968384732363328559)
    ·
      refine ⟨27347405952577098544992839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18231603968384732363328559 27347405952577098544992839)
      ·
        refine ⟨41021108928865647817489259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27347405952577098544992839 41021108928865647817489259)
        ·
          refine ⟨61531663393298471726233889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41021108928865647817489259 61531663393298471726233889)
          ·
            refine ⟨46148747544973853794675417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61531663393298471726233889 46148747544973853794675417)
            ·
              refine ⟨34611560658730390346006563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46148747544973853794675417 34611560658730390346006563)
              ·
                refine ⟨51917340988095585519009845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34611560658730390346006563 51917340988095585519009845)
                ·
                  refine ⟨4867250717633961142407173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51917340988095585519009845 4867250717633961142407173)
                  ·
                    refine ⟨912609509556367714201345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4867250717633961142407173 912609509556367714201345)
                    ·
                      rfl

theorem cell23_5331902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_5331902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331902 prefixEnd_5331902 := by exact prefixLift 5331902
  have htrace : WordTrace (prefixWord ++ tailWord_5331902) baseStart_5331902 baseEnd_5331902 := by
    simpa [prefixWord, tailWord_5331902, baseEnd_5331902] using wordTrace_append hprefix tailTrace_5331902
  have hstable : (prefixWord ++ tailWord_5331902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331902).length < 2 ^ (prefixWord ++ tailWord_5331902).sum := by decide
  have hdescent : baseEnd_5331902 < baseStart_5331902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331952 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 1, 5, 2]
def baseStart_5331952 : Nat := 118140960795 + 5331952 * 2 ^ 59
def prefixEnd_5331952 : Nat := 4983230072969 + 3 ^ 40 * 5331952 * 2
def baseEnd_5331952 : Nat := 2737854202701827946978805

theorem tailTrace_5331952 : CollatzResearch.WordTrace tailWord_5331952 prefixEnd_5331952 2737854202701827946978805 := by
  unfold tailWord_5331952
  simp only [CollatzResearch.WordTrace]
  refine ⟨97236132989628001874079055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129648177319504002498772073 97236132989628001874079055)
  ·
    refine ⟨145854199484442002811118583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97236132989628001874079055 145854199484442002811118583)
    ·
      refine ⟨218781299226663004216677875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145854199484442002811118583 218781299226663004216677875)
      ·
        refine ⟨328171948839994506325016813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218781299226663004216677875 328171948839994506325016813)
        ·
          refine ⟨123064480814997939871881305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 328171948839994506325016813 123064480814997939871881305)
          ·
            refine ⟨92298360611248454903910979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123064480814997939871881305 92298360611248454903910979)
            ·
              refine ⟨138447540916872682355866469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92298360611248454903910979 138447540916872682355866469)
              ·
                refine ⟨25958913921913627941724963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138447540916872682355866469 25958913921913627941724963)
                ·
                  refine ⟨38938370882870441912587445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25958913921913627941724963 38938370882870441912587445)
                  ·
                    refine ⟨3650472270269103929305073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38938370882870441912587445 3650472270269103929305073)
                    ·
                      refine ⟨2737854202701827946978805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3650472270269103929305073 2737854202701827946978805)
                      ·
                        rfl

theorem cell23_5331952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 1, 5, 2].length) (baseStart_5331952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331952 prefixEnd_5331952 := by exact prefixLift 5331952
  have htrace : WordTrace (prefixWord ++ tailWord_5331952) baseStart_5331952 baseEnd_5331952 := by
    simpa [prefixWord, tailWord_5331952, baseEnd_5331952] using wordTrace_append hprefix tailTrace_5331952
  have hstable : (prefixWord ++ tailWord_5331952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331952).length < 2 ^ (prefixWord ++ tailWord_5331952).sum := by decide
  have hdescent : baseEnd_5331952 < baseStart_5331952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331969 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 1, 5, 2]
def baseStart_5331969 : Nat := 118140960795 + 5331969 * 2 ^ 59
def prefixEnd_5331969 : Nat := 4983230072969 + 3 ^ 40 * 5331969 * 2
def baseEnd_5331969 : Nat := 2737862931872954380466227

theorem tailTrace_5331969 : CollatzResearch.WordTrace tailWord_5331969 prefixEnd_5331969 2737862931872954380466227 := by
  unfold tailWord_5331969
  simp only [CollatzResearch.WordTrace]
  refine ⟨194472886020194415651526961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129648590680129610434351307 194472886020194415651526961)
  ·
    refine ⟨145854664515145811738645221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194472886020194415651526961 145854664515145811738645221)
    ·
      refine ⟨27347749596589839700995979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145854664515145811738645221 27347749596589839700995979)
      ·
        refine ⟨41021624394884759551493969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27347749596589839700995979 41021624394884759551493969)
        ·
          refine ⟨30766218296163569663620477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41021624394884759551493969 30766218296163569663620477)
          ·
            refine ⟨11537331861061338623857679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30766218296163569663620477 11537331861061338623857679)
            ·
              refine ⟨17305997791592007935786519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11537331861061338623857679 17305997791592007935786519)
              ·
                refine ⟨25958996687388011903679779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17305997791592007935786519 25958996687388011903679779)
                ·
                  refine ⟨38938495031082017855519669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25958996687388011903679779 38938495031082017855519669)
                  ·
                    refine ⟨3650483909163939173954969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38938495031082017855519669 3650483909163939173954969)
                    ·
                      refine ⟨2737862931872954380466227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3650483909163939173954969 2737862931872954380466227)
                      ·
                        rfl

theorem cell23_5331969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_5331969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331969 prefixEnd_5331969 := by exact prefixLift 5331969
  have htrace : WordTrace (prefixWord ++ tailWord_5331969) baseStart_5331969 baseEnd_5331969 := by
    simpa [prefixWord, tailWord_5331969, baseEnd_5331969] using wordTrace_append hprefix tailTrace_5331969
  have hstable : (prefixWord ++ tailWord_5331969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331969).length < 2 ^ (prefixWord ++ tailWord_5331969).sum := by decide
  have hdescent : baseEnd_5331969 < baseStart_5331969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331970 : List Nat := [3, 4, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_5331970 : Nat := 118140960795 + 5331970 * 2 ^ 59
def prefixEnd_5331970 : Nat := 4983230072969 + 3 ^ 40 * 5331970 * 2
def baseEnd_5331970 : Nat := 912621148451202958851241

theorem tailTrace_5331970 : CollatzResearch.WordTrace tailWord_5331970 prefixEnd_5331970 912621148451202958851241 := by
  unfold tailWord_5331970
  simp only [CollatzResearch.WordTrace]
  refine ⟨48618230623297698205578341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129648614995460528548208909 48618230623297698205578341)
  ·
    refine ⟨9115918241868318413545939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48618230623297698205578341 9115918241868318413545939)
    ·
      refine ⟨13673877362802477620318909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9115918241868318413545939 13673877362802477620318909)
      ·
        refine ⟨5127704011050929107619591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13673877362802477620318909 5127704011050929107619591)
        ·
          refine ⟨7691556016576393661429387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5127704011050929107619591 7691556016576393661429387)
          ·
            refine ⟨11537334024864590492144081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7691556016576393661429387 11537334024864590492144081)
            ·
              refine ⟨8653000518648442869108061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11537334024864590492144081 8653000518648442869108061)
              ·
                refine ⟨3244875194493166075915523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8653000518648442869108061 3244875194493166075915523)
                ·
                  refine ⟨4867312791739749113873285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3244875194493166075915523 4867312791739749113873285)
                  ·
                    refine ⟨912621148451202958851241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4867312791739749113873285 912621148451202958851241)
                    ·
                      rfl

theorem cell23_5331970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_5331970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331970 prefixEnd_5331970 := by exact prefixLift 5331970
  have htrace : WordTrace (prefixWord ++ tailWord_5331970) baseStart_5331970 baseEnd_5331970 := by
    simpa [prefixWord, tailWord_5331970, baseEnd_5331970] using wordTrace_append hprefix tailTrace_5331970
  have hstable : (prefixWord ++ tailWord_5331970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331970).length < 2 ^ (prefixWord ++ tailWord_5331970).sum := by decide
  have hdescent : baseEnd_5331970 < baseStart_5331970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331976 : List Nat := [2, 1, 3, 2, 1, 3, 1, 5, 1, 1, 3]
def baseStart_5331976 : Nat := 118140960795 + 5331976 * 2 ^ 59
def prefixEnd_5331976 : Nat := 4983230072969 + 3 ^ 40 * 5331976 * 2
def baseEnd_5331976 : Nat := 2737866526237535853078695

theorem tailTrace_5331976 : CollatzResearch.WordTrace tailWord_5331976 prefixEnd_5331976 2737866526237535853078695 := by
  unfold tailWord_5331976
  simp only [CollatzResearch.WordTrace]
  refine ⟨97236570665584527923515891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129648760887446037231354521 97236570665584527923515891)
  ·
    refine ⟨145854855998376791885273837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97236570665584527923515891 145854855998376791885273837)
    ·
      refine ⟨54695570999391296956977689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145854855998376791885273837 54695570999391296956977689)
      ·
        refine ⟨41021678249543472717733267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54695570999391296956977689 41021678249543472717733267)
        ·
          refine ⟨61532517374315209076599901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41021678249543472717733267 61532517374315209076599901)
          ·
            refine ⟨23074694015368203403724963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61532517374315209076599901 23074694015368203403724963)
            ·
              refine ⟨34612041023052305105587445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23074694015368203403724963 34612041023052305105587445)
              ·
                refine ⟨3244878845911153603648823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34612041023052305105587445 3244878845911153603648823)
                ·
                  refine ⟨4867318268866730405473235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3244878845911153603648823 4867318268866730405473235)
                  ·
                    refine ⟨7300977403300095608209853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4867318268866730405473235 7300977403300095608209853)
                    ·
                      refine ⟨2737866526237535853078695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7300977403300095608209853 2737866526237535853078695)
                      ·
                        rfl

theorem cell23_5331976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_5331976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331976 prefixEnd_5331976 := by exact prefixLift 5331976
  have htrace : WordTrace (prefixWord ++ tailWord_5331976) baseStart_5331976 baseEnd_5331976 := by
    simpa [prefixWord, tailWord_5331976, baseEnd_5331976] using wordTrace_append hprefix tailTrace_5331976
  have hstable : (prefixWord ++ tailWord_5331976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331976).length < 2 ^ (prefixWord ++ tailWord_5331976).sum := by decide
  have hdescent : baseEnd_5331976 < baseStart_5331976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331979 : List Nat := [1, 1, 1, 1, 6, 2, 4, 1, 1, 5]
def baseStart_5331979 : Nat := 118140960795 + 5331979 * 2 ^ 59
def prefixEnd_5331979 : Nat := 4983230072969 + 3 ^ 40 * 5331979 * 2
def baseEnd_5331979 : Nat := 912622688893166447113727

theorem tailTrace_5331979 : CollatzResearch.WordTrace tailWord_5331979 prefixEnd_5331979 912622688893166447113727 := by
  unfold tailWord_5331979
  simp only [CollatzResearch.WordTrace]
  refine ⟨194473250750158187359390991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129648833833438791572927327 194473250750158187359390991)
  ·
    refine ⟨291709876125237281039086487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194473250750158187359390991 291709876125237281039086487)
    ·
      refine ⟨437564814187855921558629731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291709876125237281039086487 437564814187855921558629731)
      ·
        refine ⟨656347221281783882337944597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437564814187855921558629731 656347221281783882337944597)
        ·
          refine ⟨30766275997583619484591153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 656347221281783882337944597 30766275997583619484591153)
          ·
            refine ⟨23074706998187714613443365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30766275997583619484591153 23074706998187714613443365)
            ·
              refine ⟨4326507562160196490020631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23074706998187714613443365 4326507562160196490020631)
              ·
                refine ⟨6489761343240294735030947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4326507562160196490020631 6489761343240294735030947)
                ·
                  refine ⟨9734642014860442102546421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6489761343240294735030947 9734642014860442102546421)
                  ·
                    refine ⟨912622688893166447113727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9734642014860442102546421 912622688893166447113727)
                    ·
                      rfl

theorem cell23_5331979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 1, 5].length) (baseStart_5331979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331979 prefixEnd_5331979 := by exact prefixLift 5331979
  have htrace : WordTrace (prefixWord ++ tailWord_5331979) baseStart_5331979 baseEnd_5331979 := by
    simpa [prefixWord, tailWord_5331979, baseEnd_5331979] using wordTrace_append hprefix tailTrace_5331979
  have hstable : (prefixWord ++ tailWord_5331979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331979).length < 2 ^ (prefixWord ++ tailWord_5331979).sum := by decide
  have hdescent : baseEnd_5331979 < baseStart_5331979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5331985 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 5]
def baseStart_5331985 : Nat := 118140960795 + 5331985 * 2 ^ 59
def prefixEnd_5331985 : Nat := 4983230072969 + 3 ^ 40 * 5331985 * 2
def baseEnd_5331985 : Nat := 2737871147563426317866153

theorem tailTrace_5331985 : CollatzResearch.WordTrace tailWord_5331985 prefixEnd_5331985 2737871147563426317866153 := by
  unfold tailWord_5331985
  simp only [CollatzResearch.WordTrace]
  refine ⟨194473469588136450384109409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129648979725424300256072939 194473469588136450384109409)
  ·
    refine ⟨145855102191102337788082057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194473469588136450384109409 145855102191102337788082057)
    ·
      refine ⟨109391326643326753341061543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145855102191102337788082057 109391326643326753341061543)
      ·
        refine ⟨164086989964990130011592315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109391326643326753341061543 164086989964990130011592315)
        ·
          refine ⟨246130484947485195017388473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164086989964990130011592315 246130484947485195017388473)
          ·
            refine ⟨184597863710613896263041355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246130484947485195017388473 184597863710613896263041355)
            ·
              refine ⟨276896795565920844394562033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184597863710613896263041355 276896795565920844394562033)
              ·
                refine ⟨207672596674440633295921525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276896795565920844394562033 207672596674440633295921525)
                ·
                  refine ⟨19469305938228809371492643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 207672596674440633295921525 19469305938228809371492643)
                  ·
                    refine ⟨29203958907343214057238965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19469305938228809371492643 29203958907343214057238965)
                    ·
                      refine ⟨2737871147563426317866153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29203958907343214057238965 2737871147563426317866153)
                      ·
                        rfl

theorem cell23_5331985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_5331985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5331985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5331985 prefixEnd_5331985 := by exact prefixLift 5331985
  have htrace : WordTrace (prefixWord ++ tailWord_5331985) baseStart_5331985 baseEnd_5331985 := by
    simpa [prefixWord, tailWord_5331985, baseEnd_5331985] using wordTrace_append hprefix tailTrace_5331985
  have hstable : (prefixWord ++ tailWord_5331985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5331985).length < 2 ^ (prefixWord ++ tailWord_5331985).sum := by decide
  have hdescent : baseEnd_5331985 < baseStart_5331985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5331985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332002 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_5332002 : Nat := 118140960795 + 5332002 * 2 ^ 59
def prefixEnd_5332002 : Nat := 4983230072969 + 3 ^ 40 * 5332002 * 2
def baseEnd_5332002 : Nat := 2737879876734552751353575

theorem tailTrace_5332002 : CollatzResearch.WordTrace tailWord_5332002 prefixEnd_5332002 2737879876734552751353575 := by
  unfold tailWord_5332002
  simp only [CollatzResearch.WordTrace]
  refine ⟨48618522407268715571869565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129649393086049908191652173 48618522407268715571869565)
  ·
    refine ⟨18231945902725768339451087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48618522407268715571869565 18231945902725768339451087)
    ·
      refine ⟨27347918854088652509176631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18231945902725768339451087 27347918854088652509176631)
      ·
        refine ⟨41021878281132978763764947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27347918854088652509176631 41021878281132978763764947)
        ·
          refine ⟨61532817421699468145647421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41021878281132978763764947 61532817421699468145647421)
          ·
            refine ⟨23074806533137300554617783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61532817421699468145647421 23074806533137300554617783)
            ·
              refine ⟨34612209799705950831926675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23074806533137300554617783 34612209799705950831926675)
              ·
                refine ⟨51918314699558926247890013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34612209799705950831926675 51918314699558926247890013)
                ·
                  refine ⟨19469368012334597342958755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51918314699558926247890013 19469368012334597342958755)
                  ·
                    refine ⟨29204052018501896014438133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19469368012334597342958755 29204052018501896014438133)
                    ·
                      refine ⟨2737879876734552751353575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29204052018501896014438133 2737879876734552751353575)
                      ·
                        rfl

theorem cell23_5332002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_5332002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332002 prefixEnd_5332002 := by exact prefixLift 5332002
  have htrace : WordTrace (prefixWord ++ tailWord_5332002) baseStart_5332002 baseEnd_5332002 := by
    simpa [prefixWord, tailWord_5332002, baseEnd_5332002] using wordTrace_append hprefix tailTrace_5332002
  have hstable : (prefixWord ++ tailWord_5332002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332002).length < 2 ^ (prefixWord ++ tailWord_5332002).sum := by decide
  have hdescent : baseEnd_5332002 < baseStart_5332002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332005 : List Nat := [1, 3, 1, 2, 2, 2, 2, 10]
def baseStart_5332005 : Nat := 118140960795 + 5332005 * 2 ^ 59
def prefixEnd_5332005 : Nat := 4983230072969 + 3 ^ 40 * 5332005 * 2
def baseEnd_5332005 : Nat := 101403015450982082948743

theorem tailTrace_5332005 : CollatzResearch.WordTrace tailWord_5332005 prefixEnd_5332005 101403015450982082948743 := by
  unfold tailWord_5332005
  simp only [CollatzResearch.WordTrace]
  refine ⟨194474199048063993799837469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129649466032042662533224979 194474199048063993799837469)
  ·
    refine ⟨72927824643023997674939051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194474199048063993799837469 72927824643023997674939051)
    ·
      refine ⟨109391736964535996512408577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72927824643023997674939051 109391736964535996512408577)
      ·
        refine ⟨82043802723401997384306433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109391736964535996512408577 82043802723401997384306433)
        ·
          refine ⟨61532852042551498038229825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82043802723401997384306433 61532852042551498038229825)
          ·
            refine ⟨46149639031913623528672369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61532852042551498038229825 46149639031913623528672369)
            ·
              refine ⟨34612229273935217646504277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46149639031913623528672369 34612229273935217646504277)
              ·
                refine ⟨101403015450982082948743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34612229273935217646504277 101403015450982082948743)
                ·
                  rfl

theorem cell23_5332005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 10].length) (baseStart_5332005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332005 prefixEnd_5332005 := by exact prefixLift 5332005
  have htrace : WordTrace (prefixWord ++ tailWord_5332005) baseStart_5332005 baseEnd_5332005 := by
    simpa [prefixWord, tailWord_5332005, baseEnd_5332005] using wordTrace_append hprefix tailTrace_5332005
  have hstable : (prefixWord ++ tailWord_5332005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332005).length < 2 ^ (prefixWord ++ tailWord_5332005).sum := by decide
  have hdescent : baseEnd_5332005 < baseStart_5332005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332032 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 3]
def baseStart_5332032 : Nat := 118140960795 + 5332032 * 2 ^ 59
def prefixEnd_5332032 : Nat := 4983230072969 + 3 ^ 40 * 5332032 * 2
def baseEnd_5332032 : Nat := 2737895281154187633978437

theorem tailTrace_5332032 : CollatzResearch.WordTrace tailWord_5332032 prefixEnd_5332032 2737895281154187633978437 := by
  unfold tailWord_5332032
  simp only [CollatzResearch.WordTrace]
  refine ⟨97237591909483088705535175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129650122545977451607380233 97237591909483088705535175)
  ·
    refine ⟨145856387864224633058302763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97237591909483088705535175 145856387864224633058302763)
    ·
      refine ⟨218784581796336949587454145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145856387864224633058302763 218784581796336949587454145)
      ·
        refine ⟨164088436347252712190590609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218784581796336949587454145 164088436347252712190590609)
        ·
          refine ⟨123066327260439534142942957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164088436347252712190590609 123066327260439534142942957)
          ·
            refine ⟨46149872722664825303603609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123066327260439534142942957 46149872722664825303603609)
            ·
              refine ⟨34612404541998618977702707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46149872722664825303603609 34612404541998618977702707)
              ·
                refine ⟨51918606812997928466554061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34612404541998618977702707 51918606812997928466554061)
                ·
                  refine ⟨19469477554874223174957773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51918606812997928466554061 19469477554874223174957773)
                  ·
                    refine ⟨7301054083077833690609165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19469477554874223174957773 7301054083077833690609165)
                    ·
                      refine ⟨2737895281154187633978437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7301054083077833690609165 2737895281154187633978437)
                      ·
                        rfl

theorem cell23_5332032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_5332032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332032 prefixEnd_5332032 := by exact prefixLift 5332032
  have htrace : WordTrace (prefixWord ++ tailWord_5332032) baseStart_5332032 baseEnd_5332032 := by
    simpa [prefixWord, tailWord_5332032, baseEnd_5332032] using wordTrace_append hprefix tailTrace_5332032
  have hstable : (prefixWord ++ tailWord_5332032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332032).length < 2 ^ (prefixWord ++ tailWord_5332032).sum := by decide
  have hdescent : baseEnd_5332032 < baseStart_5332032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332049 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 4, 1, 3]
def baseStart_5332049 : Nat := 118140960795 + 5332049 * 2 ^ 59
def prefixEnd_5332049 : Nat := 4983230072969 + 3 ^ 40 * 5332049 * 2
def baseEnd_5332049 : Nat := 2737904010325314067465859

theorem tailTrace_5332049 : CollatzResearch.WordTrace tailWord_5332049 prefixEnd_5332049 2737904010325314067465859 := by
  unfold tailWord_5332049
  simp only [CollatzResearch.WordTrace]
  refine ⟨194475803859904589314439201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129650535906603059542959467 194475803859904589314439201)
  ·
    refine ⟨145856852894928441985829401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194475803859904589314439201 145856852894928441985829401)
    ·
      refine ⟨109392639671196331489372051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145856852894928441985829401 109392639671196331489372051)
      ·
        refine ⟨164088959506794497234058077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109392639671196331489372051 164088959506794497234058077)
        ·
          refine ⟨61533359815047936462771779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164088959506794497234058077 61533359815047936462771779)
          ·
            refine ⟨92300039722571904694157669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61533359815047936462771779 92300039722571904694157669)
            ·
              refine ⟨17306257447982232130154563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92300039722571904694157669 17306257447982232130154563)
              ·
                refine ⟨25959386171973348195231845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17306257447982232130154563 25959386171973348195231845)
                ·
                  refine ⟨4867384907245002786605971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25959386171973348195231845 4867384907245002786605971)
                  ·
                    refine ⟨7301077360867504179908957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4867384907245002786605971 7301077360867504179908957)
                    ·
                      refine ⟨2737904010325314067465859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7301077360867504179908957 2737904010325314067465859)
                      ·
                        rfl

theorem cell23_5332049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 1, 3].length) (baseStart_5332049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332049 prefixEnd_5332049 := by exact prefixLift 5332049
  have htrace : WordTrace (prefixWord ++ tailWord_5332049) baseStart_5332049 baseEnd_5332049 := by
    simpa [prefixWord, tailWord_5332049, baseEnd_5332049] using wordTrace_append hprefix tailTrace_5332049
  have hstable : (prefixWord ++ tailWord_5332049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332049).length < 2 ^ (prefixWord ++ tailWord_5332049).sum := by decide
  have hdescent : baseEnd_5332049 < baseStart_5332049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332075 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 9]
def baseStart_5332075 : Nat := 118140960795 + 5332075 * 2 ^ 59
def prefixEnd_5332075 : Nat := 4983230072969 + 3 ^ 40 * 5332075 * 2
def baseEnd_5332075 : Nat := 2737917360822330965740739

theorem tailTrace_5332075 : CollatzResearch.WordTrace tailWord_5332075 prefixEnd_5332075 2737917360822330965740739 := by
  unfold tailWord_5332075
  simp only [CollatzResearch.WordTrace]
  refine ⟨194476752157810395754885679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129651168105206930503257119 194476752157810395754885679)
  ·
    refine ⟨291715128236715593632328519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194476752157810395754885679 291715128236715593632328519)
    ·
      refine ⟨437572692355073390448492779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291715128236715593632328519 437572692355073390448492779)
      ·
        refine ⟨656359038532610085672739169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437572692355073390448492779 656359038532610085672739169)
        ·
          refine ⟨492269278899457564254554377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 656359038532610085672739169 492269278899457564254554377)
          ·
            refine ⟨369201959174593173190915783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 492269278899457564254554377 369201959174593173190915783)
            ·
              refine ⟨553802938761889759786373675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369201959174593173190915783 553802938761889759786373675)
              ·
                refine ⟨830704408142834639679560513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553802938761889759786373675 830704408142834639679560513)
                ·
                  refine ⟨623028306107125979759670385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 830704408142834639679560513 623028306107125979759670385)
                  ·
                    refine ⟨467271229580344484819752789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 623028306107125979759670385 467271229580344484819752789)
                    ·
                      refine ⟨2737917360822330965740739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 467271229580344484819752789 2737917360822330965740739)
                      ·
                        rfl

theorem cell23_5332075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 9].length) (baseStart_5332075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332075 prefixEnd_5332075 := by exact prefixLift 5332075
  have htrace : WordTrace (prefixWord ++ tailWord_5332075) baseStart_5332075 baseEnd_5332075 := by
    simpa [prefixWord, tailWord_5332075, baseEnd_5332075] using wordTrace_append hprefix tailTrace_5332075
  have hstable : (prefixWord ++ tailWord_5332075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332075).length < 2 ^ (prefixWord ++ tailWord_5332075).sum := by decide
  have hdescent : baseEnd_5332075 < baseStart_5332075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332092 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_5332092 : Nat := 118140960795 + 5332092 * 2 ^ 59
def prefixEnd_5332092 : Nat := 4983230072969 + 3 ^ 40 * 5332092 * 2
def baseEnd_5332092 : Nat := 2737926089993457399228161

theorem tailTrace_5332092 : CollatzResearch.WordTrace tailWord_5332092 prefixEnd_5332092 2737926089993457399228161 := by
  unfold tailWord_5332092
  simp only [CollatzResearch.WordTrace]
  refine ⟨97238686099374403829127265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129651581465832538438836353 97238686099374403829127265)
  ·
    refine ⟨72929014574530802871845449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97238686099374403829127265 72929014574530802871845449)
    ·
      refine ⟨54696760930898102153884087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72929014574530802871845449 54696760930898102153884087)
      ·
        refine ⟨82045141396347153230826131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54696760930898102153884087 82045141396347153230826131)
        ·
          refine ⟨123067712094520729846239197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82045141396347153230826131 123067712094520729846239197)
          ·
            refine ⟨46150392035445273692339699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123067712094520729846239197 46150392035445273692339699)
            ·
              refine ⟨69225588053167910538509549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46150392035445273692339699 69225588053167910538509549)
              ·
                refine ⟨25959595519937966451941081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69225588053167910538509549 25959595519937966451941081)
                ·
                  refine ⟨19469696639953474838955811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25959595519937966451941081 19469696639953474838955811)
                  ·
                    refine ⟨29204544959930212258433717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19469696639953474838955811 29204544959930212258433717)
                    ·
                      refine ⟨2737926089993457399228161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29204544959930212258433717 2737926089993457399228161)
                      ·
                        rfl

theorem cell23_5332092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_5332092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332092 prefixEnd_5332092 := by exact prefixLift 5332092
  have htrace : WordTrace (prefixWord ++ tailWord_5332092) baseStart_5332092 baseEnd_5332092 := by
    simpa [prefixWord, tailWord_5332092, baseEnd_5332092] using wordTrace_append hprefix tailTrace_5332092
  have hstable : (prefixWord ++ tailWord_5332092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332092).length < 2 ^ (prefixWord ++ tailWord_5332092).sum := by decide
  have hdescent : baseEnd_5332092 < baseStart_5332092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332093 : List Nat := [1, 4, 1, 1, 3, 1, 5, 1, 1, 3, 2]
def baseStart_5332093 : Nat := 118140960795 + 5332093 * 2 ^ 59
def prefixEnd_5332093 : Nat := 4983230072969 + 3 ^ 40 * 5332093 * 2
def baseEnd_5332093 : Nat := 2737926603474111895315657

theorem tailTrace_5332093 : CollatzResearch.WordTrace tailWord_5332093 prefixEnd_5332093 2737926603474111895315657 := by
  unfold tailWord_5332093
  simp only [CollatzResearch.WordTrace]
  refine ⟨194477408671745184829040933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129651605781163456552693955 194477408671745184829040933)
  ·
    refine ⟨36464514125952222155445175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194477408671745184829040933 36464514125952222155445175)
    ·
      refine ⟨54696771188928333233167763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36464514125952222155445175 54696771188928333233167763)
      ·
        refine ⟨82045156783392499849751645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54696771188928333233167763 82045156783392499849751645)
        ·
          refine ⟨30766933793772187443656867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82045156783392499849751645 30766933793772187443656867)
          ·
            refine ⟨46150400690658281165485301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30766933793772187443656867 46150400690658281165485301)
            ·
              refine ⟨4326600064749213859264247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46150400690658281165485301 4326600064749213859264247)
              ·
                refine ⟨6489900097123820788896371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4326600064749213859264247 6489900097123820788896371)
                ·
                  refine ⟨9734850145685731183344557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6489900097123820788896371 9734850145685731183344557)
                  ·
                    refine ⟨3650568804632149193754209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9734850145685731183344557 3650568804632149193754209)
                    ·
                      refine ⟨2737926603474111895315657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3650568804632149193754209 2737926603474111895315657)
                      ·
                        rfl

theorem cell23_5332093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_5332093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332093 prefixEnd_5332093 := by exact prefixLift 5332093
  have htrace : WordTrace (prefixWord ++ tailWord_5332093) baseStart_5332093 baseEnd_5332093 := by
    simpa [prefixWord, tailWord_5332093, baseEnd_5332093] using wordTrace_append hprefix tailTrace_5332093
  have hstable : (prefixWord ++ tailWord_5332093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332093).length < 2 ^ (prefixWord ++ tailWord_5332093).sum := by decide
  have hdescent : baseEnd_5332093 < baseStart_5332093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332119 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 4]
def baseStart_5332119 : Nat := 118140960795 + 5332119 * 2 ^ 59
def prefixEnd_5332119 : Nat := 4983230072969 + 3 ^ 40 * 5332119 * 2
def baseEnd_5332119 : Nat := 2737939953971128793590537

theorem tailTrace_5332119 : CollatzResearch.WordTrace tailWord_5332119 prefixEnd_5332119 2737939953971128793590537 := by
  unfold tailWord_5332119
  simp only [CollatzResearch.WordTrace]
  refine ⟨194478356969650991269487411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129652237979767327512991607 194478356969650991269487411)
  ·
    refine ⟨291717535454476486904231117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194478356969650991269487411 291717535454476486904231117)
    ·
      refine ⟨109394075795428682589086669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291717535454476486904231117 109394075795428682589086669)
      ·
        refine ⟨41022778423285755970907501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109394075795428682589086669 41022778423285755970907501)
        ·
          refine ⟨15383541908732158489090313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41022778423285755970907501 15383541908732158489090313)
          ·
            refine ⟨11537656431549118866817735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15383541908732158489090313 11537656431549118866817735)
            ·
              refine ⟨17306484647323678300226603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11537656431549118866817735 17306484647323678300226603)
              ·
                refine ⟨25959726970985517450339905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17306484647323678300226603 25959726970985517450339905)
                ·
                  refine ⟨19469795228239138087754929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25959726970985517450339905 19469795228239138087754929)
                  ·
                    refine ⟨14602346421179353565816197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19469795228239138087754929 14602346421179353565816197)
                    ·
                      refine ⟨2737939953971128793590537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14602346421179353565816197 2737939953971128793590537)
                      ·
                        rfl

theorem cell23_5332119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_5332119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332119 prefixEnd_5332119 := by exact prefixLift 5332119
  have htrace : WordTrace (prefixWord ++ tailWord_5332119) baseStart_5332119 baseEnd_5332119 := by
    simpa [prefixWord, tailWord_5332119, baseEnd_5332119] using wordTrace_append hprefix tailTrace_5332119
  have hstable : (prefixWord ++ tailWord_5332119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332119).length < 2 ^ (prefixWord ++ tailWord_5332119).sum := by decide
  have hdescent : baseEnd_5332119 < baseStart_5332119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332146 : List Nat := [3, 2, 1, 1, 1, 5, 2, 3, 5]
def baseStart_5332146 : Nat := 118140960795 + 5332146 * 2 ^ 59
def prefixEnd_5332146 : Nat := 4983230072969 + 3 ^ 40 * 5332146 * 2
def baseEnd_5332146 : Nat := 304217090883200020883657

theorem tailTrace_5332146 : CollatzResearch.WordTrace tailWord_5332146 prefixEnd_5332146 304217090883200020883657 := by
  unfold tailWord_5332146
  simp only [CollatzResearch.WordTrace]
  refine ⟨48619835435138293720180073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129652894493702116587146861 48619835435138293720180073)
  ·
    refine ⟨36464876576353720290135055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48619835435138293720180073 36464876576353720290135055)
    ·
      refine ⟨54697314864530580435202583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36464876576353720290135055 54697314864530580435202583)
      ·
        refine ⟨82045972296795870652803875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54697314864530580435202583 82045972296795870652803875)
        ·
          refine ⟨123068958445193805979205813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82045972296795870652803875 123068958445193805979205813)
          ·
            refine ⟨11537714854236919310550545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123068958445193805979205813 11537714854236919310550545)
            ·
              refine ⟨8653286140677689482912909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11537714854236919310550545 8653286140677689482912909)
              ·
                refine ⟨3244982302754133556092341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8653286140677689482912909 3244982302754133556092341)
                ·
                  refine ⟨304217090883200020883657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3244982302754133556092341 304217090883200020883657)
                  ·
                    rfl

theorem cell23_5332146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_5332146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332146 prefixEnd_5332146 := by exact prefixLift 5332146
  have htrace : WordTrace (prefixWord ++ tailWord_5332146) baseStart_5332146 baseEnd_5332146 := by
    simpa [prefixWord, tailWord_5332146, baseEnd_5332146] using wordTrace_append hprefix tailTrace_5332146
  have hstable : (prefixWord ++ tailWord_5332146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332146).length < 2 ^ (prefixWord ++ tailWord_5332146).sum := by decide
  have hdescent : baseEnd_5332146 < baseStart_5332146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332152 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 1, 2, 5]
def baseStart_5332152 : Nat := 118140960795 + 5332152 * 2 ^ 59
def prefixEnd_5332152 : Nat := 4983230072969 + 3 ^ 40 * 5332152 * 2
def baseEnd_5332152 : Nat := 2737956898832727164477885

theorem tailTrace_5332152 : CollatzResearch.WordTrace tailWord_5332152 prefixEnd_5332152 2737956898832727164477885 := by
  unfold tailWord_5332152
  simp only [CollatzResearch.WordTrace]
  refine ⟨97239780289265718952719355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129653040385687625270292473 97239780289265718952719355)
  ·
    refine ⟨145859670433898578429079033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97239780289265718952719355 145859670433898578429079033)
    ·
      refine ⟨109394752825423933821809275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145859670433898578429079033 109394752825423933821809275)
      ·
        refine ⟨164092129238135900732713913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109394752825423933821809275 164092129238135900732713913)
        ·
          refine ⟨123069096928601925549535435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164092129238135900732713913 123069096928601925549535435)
          ·
            refine ⟨184603645392902888324303153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123069096928601925549535435 184603645392902888324303153)
            ·
              refine ⟨138452734044677166243227365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184603645392902888324303153 138452734044677166243227365)
              ·
                refine ⟨25959887633376968670605131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138452734044677166243227365 25959887633376968670605131)
                ·
                  refine ⟨38939831450065453005907697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25959887633376968670605131 38939831450065453005907697)
                  ·
                    refine ⟨29204873587549089754430773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38939831450065453005907697 29204873587549089754430773)
                    ·
                      refine ⟨2737956898832727164477885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29204873587549089754430773 2737956898832727164477885)
                      ·
                        rfl

theorem cell23_5332152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_5332152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332152 prefixEnd_5332152 := by exact prefixLift 5332152
  have htrace : WordTrace (prefixWord ++ tailWord_5332152) baseStart_5332152 baseEnd_5332152 := by
    simpa [prefixWord, tailWord_5332152, baseEnd_5332152] using wordTrace_append hprefix tailTrace_5332152
  have hstable : (prefixWord ++ tailWord_5332152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332152).length < 2 ^ (prefixWord ++ tailWord_5332152).sum := by decide
  have hdescent : baseEnd_5332152 < baseStart_5332152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5332236 : List Nat := [2, 2, 1, 2, 2, 3, 4, 1, 6]
def baseStart_5332236 : Nat := 118140960795 + 5332236 * 2 ^ 59
def prefixEnd_5332236 : Nat := 4983230072969 + 3 ^ 40 * 5332236 * 2
def baseEnd_5332236 : Nat := 304222225689744981758611

theorem tailTrace_5332236 : CollatzResearch.WordTrace tailWord_5332236 prefixEnd_5332236 304222225689744981758611 := by
  unfold tailWord_5332236
  simp only [CollatzResearch.WordTrace]
  refine ⟨97241312155113560125748281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129655082873484746834331041 97241312155113560125748281)
  ·
    refine ⟨72930984116335170094311211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97241312155113560125748281 72930984116335170094311211)
    ·
      refine ⟨109396476174502755141466817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72930984116335170094311211 109396476174502755141466817)
      ·
        refine ⟨82047357130877066356100113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109396476174502755141466817 82047357130877066356100113)
        ·
          refine ⟨61535517848157799767075085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82047357130877066356100113 61535517848157799767075085)
          ·
            refine ⟨23075819193059174912653157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61535517848157799767075085 23075819193059174912653157)
            ·
              refine ⟨4326716098698595296122467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23075819193059174912653157 4326716098698595296122467)
              ·
                refine ⟨6490074148047892944183701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4326716098698595296122467 6490074148047892944183701)
                ·
                  refine ⟨304222225689744981758611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6490074148047892944183701 304222225689744981758611)
                  ·
                    rfl

theorem cell23_5332236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 6].length) (baseStart_5332236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5332236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5332236 prefixEnd_5332236 := by exact prefixLift 5332236
  have htrace : WordTrace (prefixWord ++ tailWord_5332236) baseStart_5332236 baseEnd_5332236 := by
    simpa [prefixWord, tailWord_5332236, baseEnd_5332236] using wordTrace_append hprefix tailTrace_5332236
  have hstable : (prefixWord ++ tailWord_5332236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5332236).length < 2 ^ (prefixWord ++ tailWord_5332236).sum := by decide
  have hdescent : baseEnd_5332236 < baseStart_5332236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5332236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
