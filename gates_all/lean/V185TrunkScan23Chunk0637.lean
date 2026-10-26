import V185TrunkScan23Chunk0636

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3766632 : List Nat := [2, 1, 4, 2, 2, 2, 2, 1, 1, 4, 2]
def baseStart_3766632 : Nat := 118140960795 + 3766632 * 2 ^ 59
def prefixEnd_3766632 : Nat := 4983230072969 + 3 ^ 40 * 3766632 * 2
def baseEnd_3766632 : Nat := 1934092664606012268677581

theorem tailTrace_3766632 : CollatzResearch.WordTrace tailWord_3766632 prefixEnd_3766632 1934092664606012268677581 := by
  unfold tailWord_3766632
  simp only [CollatzResearch.WordTrace]
  refine ⟨68690177645071514187907075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91586903526762018917209433 68690177645071514187907075)
  ·
    refine ⟨103035266467607271281860613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68690177645071514187907075 103035266467607271281860613)
    ·
      refine ⟨19319112462676363365348865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103035266467607271281860613 19319112462676363365348865)
      ·
        refine ⟨14489334347007272524011649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19319112462676363365348865 14489334347007272524011649)
        ·
          refine ⟨10867000760255454393008737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14489334347007272524011649 10867000760255454393008737)
          ·
            refine ⟨8150250570191590794756553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10867000760255454393008737 8150250570191590794756553)
            ·
              refine ⟨6112687927643693096067415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8150250570191590794756553 6112687927643693096067415)
              ·
                refine ⟨9169031891465539644101123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6112687927643693096067415 9169031891465539644101123)
                ·
                  refine ⟨13753547837198309466151685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9169031891465539644101123 13753547837198309466151685)
                  ·
                    refine ⟨2578790219474683024903441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13753547837198309466151685 2578790219474683024903441)
                    ·
                      refine ⟨1934092664606012268677581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2578790219474683024903441 1934092664606012268677581)
                      ·
                        rfl

theorem cell23_3766632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_3766632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766632 prefixEnd_3766632 := by exact prefixLift 3766632
  have htrace : WordTrace (prefixWord ++ tailWord_3766632) baseStart_3766632 baseEnd_3766632 := by
    simpa [prefixWord, tailWord_3766632, baseEnd_3766632] using wordTrace_append hprefix tailTrace_3766632
  have hstable : (prefixWord ++ tailWord_3766632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766632).length < 2 ^ (prefixWord ++ tailWord_3766632).sum := by decide
  have hdescent : baseEnd_3766632 < baseStart_3766632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766688 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 4]
def baseStart_3766688 : Nat := 118140960795 + 3766688 * 2 ^ 59
def prefixEnd_3766688 : Nat := 4983230072969 + 3 ^ 40 * 3766688 * 2
def baseEnd_3766688 : Nat := 1934121419522664049577323

theorem tailTrace_3766688 : CollatzResearch.WordTrace tailWord_3766688 prefixEnd_3766688 1934121419522664049577323 := by
  unfold tailWord_3766688
  simp only [CollatzResearch.WordTrace]
  refine ⟨68691198888970074969926359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91588265185293433293235145 68691198888970074969926359)
  ·
    refine ⟨103036798333455112454889539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68691198888970074969926359 103036798333455112454889539)
    ·
      refine ⟨154555197500182668682334309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103036798333455112454889539 154555197500182668682334309)
      ·
        refine ⟨28979099531284250377937683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154555197500182668682334309 28979099531284250377937683)
        ·
          refine ⟨43468649296926375566906525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28979099531284250377937683 43468649296926375566906525)
          ·
            refine ⟨16300743486347390837589947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43468649296926375566906525 16300743486347390837589947)
            ·
              refine ⟨24451115229521086256384921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16300743486347390837589947 24451115229521086256384921)
              ·
                refine ⟨18338336422140814692288691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24451115229521086256384921 18338336422140814692288691)
                ·
                  refine ⟨27507504633211222038433037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18338336422140814692288691 27507504633211222038433037)
                  ·
                    refine ⟨10315314237454208264412389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27507504633211222038433037 10315314237454208264412389)
                    ·
                      refine ⟨1934121419522664049577323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10315314237454208264412389 1934121419522664049577323)
                      ·
                        rfl

theorem cell23_3766688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_3766688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766688 prefixEnd_3766688 := by exact prefixLift 3766688
  have htrace : WordTrace (prefixWord ++ tailWord_3766688) baseStart_3766688 baseEnd_3766688 := by
    simpa [prefixWord, tailWord_3766688, baseEnd_3766688] using wordTrace_append hprefix tailTrace_3766688
  have hstable : (prefixWord ++ tailWord_3766688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766688).length < 2 ^ (prefixWord ++ tailWord_3766688).sum := by decide
  have hdescent : baseEnd_3766688 < baseStart_3766688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766718 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_3766718 : Nat := 118140960795 + 3766718 * 2 ^ 59
def prefixEnd_3766718 : Nat := 4983230072969 + 3 ^ 40 * 3766718 * 2
def baseEnd_3766718 : Nat := 1934136823942298932202185

theorem tailTrace_3766718 : CollatzResearch.WordTrace tailWord_3766718 prefixEnd_3766718 1934136823942298932202185 := by
  unfold tailWord_3766718
  simp only [CollatzResearch.WordTrace]
  refine ⟨17172936495978933132930601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91588994645220976708963205 17172936495978933132930601)
  ·
    refine ⟨12879702371984199849697951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17172936495978933132930601 12879702371984199849697951)
    ·
      refine ⟨19319553557976299774546927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12879702371984199849697951 19319553557976299774546927)
      ·
        refine ⟨28979330336964449661820391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19319553557976299774546927 28979330336964449661820391)
        ·
          refine ⟨43468995505446674492730587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28979330336964449661820391 43468995505446674492730587)
          ·
            refine ⟨65203493258170011739095881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43468995505446674492730587 65203493258170011739095881)
            ·
              refine ⟨48902619943627508804321911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65203493258170011739095881 48902619943627508804321911)
              ·
                refine ⟨73353929915441263206482867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48902619943627508804321911 73353929915441263206482867)
                ·
                  refine ⟨110030894873161894809724301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73353929915441263206482867 110030894873161894809724301)
                  ·
                    refine ⟨41261585577435710553646613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110030894873161894809724301 41261585577435710553646613)
                    ·
                      refine ⟨1934136823942298932202185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41261585577435710553646613 1934136823942298932202185)
                      ·
                        rfl

theorem cell23_3766718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_3766718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766718 prefixEnd_3766718 := by exact prefixLift 3766718
  have htrace : WordTrace (prefixWord ++ tailWord_3766718) baseStart_3766718 baseEnd_3766718 := by
    simpa [prefixWord, tailWord_3766718, baseEnd_3766718] using wordTrace_append hprefix tailTrace_3766718
  have hstable : (prefixWord ++ tailWord_3766718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766718).length < 2 ^ (prefixWord ++ tailWord_3766718).sum := by decide
  have hdescent : baseEnd_3766718 < baseStart_3766718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766728 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 8]
def baseStart_3766728 : Nat := 118140960795 + 3766728 * 2 ^ 59
def prefixEnd_3766728 : Nat := 4983230072969 + 3 ^ 40 * 3766728 * 2
def baseEnd_3766728 : Nat := 214904662083204877008571

theorem tailTrace_3766728 : CollatzResearch.WordTrace tailWord_3766728 prefixEnd_3766728 214904662083204877008571 := by
  unfold tailWord_3766728
  simp only [CollatzResearch.WordTrace]
  refine ⟨68691928348897618385654419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91589237798530157847539225 68691928348897618385654419)
  ·
    refine ⟨103037892523346427578481629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68691928348897618385654419 103037892523346427578481629)
    ·
      refine ⟨38639209696254910341930611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103037892523346427578481629 38639209696254910341930611)
      ·
        refine ⟨57958814544382365512895917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38639209696254910341930611 57958814544382365512895917)
        ·
          refine ⟨21734555454143387067335969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57958814544382365512895917 21734555454143387067335969)
          ·
            refine ⟨16300916590607540300501977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21734555454143387067335969 16300916590607540300501977)
            ·
              refine ⟨12225687442955655225376483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16300916590607540300501977 12225687442955655225376483)
              ·
                refine ⟨18338531164433482838064725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12225687442955655225376483 18338531164433482838064725)
                ·
                  refine ⟨214904662083204877008571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18338531164433482838064725 214904662083204877008571)
                  ·
                    rfl

theorem cell23_3766728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 8].length) (baseStart_3766728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766728 prefixEnd_3766728 := by exact prefixLift 3766728
  have htrace : WordTrace (prefixWord ++ tailWord_3766728) baseStart_3766728 baseEnd_3766728 := by
    simpa [prefixWord, tailWord_3766728, baseEnd_3766728] using wordTrace_append hprefix tailTrace_3766728
  have hstable : (prefixWord ++ tailWord_3766728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766728).length < 2 ^ (prefixWord ++ tailWord_3766728).sum := by decide
  have hdescent : baseEnd_3766728 < baseStart_3766728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766742 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_3766742 : Nat := 118140960795 + 3766742 * 2 ^ 59
def prefixEnd_3766742 : Nat := 4983230072969 + 3 ^ 40 * 3766742 * 2
def baseEnd_3766742 : Nat := 1934149147478006838302075

theorem tailTrace_3766742 : CollatzResearch.WordTrace tailWord_3766742 prefixEnd_3766742 1934149147478006838302075 := by
  unfold tailWord_3766742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8586522957484032322644905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91589578213163011441545653 8586522957484032322644905)
  ·
    refine ⟨6439892218113024241983679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8586522957484032322644905 6439892218113024241983679)
    ·
      refine ⟨9659838327169536362975519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6439892218113024241983679 9659838327169536362975519)
      ·
        refine ⟨14489757490754304544463279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9659838327169536362975519 14489757490754304544463279)
        ·
          refine ⟨21734636236131456816694919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14489757490754304544463279 21734636236131456816694919)
          ·
            refine ⟨32601954354197185225042379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21734636236131456816694919 32601954354197185225042379)
            ·
              refine ⟨48902931531295777837563569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32601954354197185225042379 48902931531295777837563569)
              ·
                refine ⟨36677198648471833378172677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48902931531295777837563569 36677198648471833378172677)
                ·
                  refine ⟨6876974746588468758407377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36677198648471833378172677 6876974746588468758407377)
                  ·
                    refine ⟨5157731059941351568805533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6876974746588468758407377 5157731059941351568805533)
                    ·
                      refine ⟨1934149147478006838302075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5157731059941351568805533 1934149147478006838302075)
                      ·
                        rfl

theorem cell23_3766742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_3766742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766742 prefixEnd_3766742 := by exact prefixLift 3766742
  have htrace : WordTrace (prefixWord ++ tailWord_3766742) baseStart_3766742 baseEnd_3766742 := by
    simpa [prefixWord, tailWord_3766742, baseEnd_3766742] using wordTrace_append hprefix tailTrace_3766742
  have hstable : (prefixWord ++ tailWord_3766742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766742).length < 2 ^ (prefixWord ++ tailWord_3766742).sum := by decide
  have hdescent : baseEnd_3766742 < baseStart_3766742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766795 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 4]
def baseStart_3766795 : Nat := 118140960795 + 3766795 * 2 ^ 59
def prefixEnd_3766795 : Nat := 4983230072969 + 3 ^ 40 * 3766795 * 2
def baseEnd_3766795 : Nat := 1934176361952695130939331

theorem tailTrace_3766795 : CollatzResearch.WordTrace tailWord_3766795 prefixEnd_3766795 1934176361952695130939331 := by
  unfold tailWord_3766795
  simp only [CollatzResearch.WordTrace]
  refine ⟨137386300388552507213997839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91590866925701671475998559 137386300388552507213997839)
  ·
    refine ⟨206079450582828760820996759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137386300388552507213997839 206079450582828760820996759)
    ·
      refine ⟨309119175874243141231495139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206079450582828760820996759 309119175874243141231495139)
      ·
        refine ⟨463678763811364711847242709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309119175874243141231495139 463678763811364711847242709)
        ·
          refine ⟨10867471026828860433919751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 463678763811364711847242709 10867471026828860433919751)
          ·
            refine ⟨16301206540243290650879627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10867471026828860433919751 16301206540243290650879627)
            ·
              refine ⟨24451809810364935976319441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16301206540243290650879627 24451809810364935976319441)
              ·
                refine ⟨18338857357773701982239581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24451809810364935976319441 18338857357773701982239581)
                ·
                  refine ⟨6877071509165138243339843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18338857357773701982239581 6877071509165138243339843)
                  ·
                    refine ⟨10315607263747707365009765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6877071509165138243339843 10315607263747707365009765)
                    ·
                      refine ⟨1934176361952695130939331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10315607263747707365009765 1934176361952695130939331)
                      ·
                        rfl

theorem cell23_3766795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 4].length) (baseStart_3766795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766795 prefixEnd_3766795 := by exact prefixLift 3766795
  have htrace : WordTrace (prefixWord ++ tailWord_3766795) baseStart_3766795 baseEnd_3766795 := by
    simpa [prefixWord, tailWord_3766795, baseEnd_3766795] using wordTrace_append hprefix tailTrace_3766795
  have hstable : (prefixWord ++ tailWord_3766795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766795).length < 2 ^ (prefixWord ++ tailWord_3766795).sum := by decide
  have hdescent : baseEnd_3766795 < baseStart_3766795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766805 : List Nat := [1, 3, 2, 1, 3, 1, 4, 1, 1, 6]
def baseStart_3766805 : Nat := 118140960795 + 3766805 * 2 ^ 59
def prefixEnd_3766805 : Nat := 4983230072969 + 3 ^ 40 * 3766805 * 2
def baseEnd_3766805 : Nat := 644727165586413363938095

theorem tailTrace_3766805 : CollatzResearch.WordTrace tailWord_3766805 prefixEnd_3766805 644727165586413363938095 := by
  unfold tailWord_3766805
  simp only [CollatzResearch.WordTrace]
  refine ⟨137386665118516278921861869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91591110079010852614574579 137386665118516278921861869)
  ·
    refine ⟨51519999419443604595698201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137386665118516278921861869 51519999419443604595698201)
    ·
      refine ⟨38639999564582703446773651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51519999419443604595698201 38639999564582703446773651)
      ·
        refine ⟨57959999346874055170160477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38639999564582703446773651 57959999346874055170160477)
        ·
          refine ⟨21734999755077770688810179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57959999346874055170160477 21734999755077770688810179)
          ·
            refine ⟨32602499632616656033215269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21734999755077770688810179 32602499632616656033215269)
            ·
              refine ⟨6112968681115623006227863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32602499632616656033215269 6112968681115623006227863)
              ·
                refine ⟨9169453021673434509341795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6112968681115623006227863 9169453021673434509341795)
                ·
                  refine ⟨13754179532510151764012693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9169453021673434509341795 13754179532510151764012693)
                  ·
                    refine ⟨644727165586413363938095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13754179532510151764012693 644727165586413363938095)
                    ·
                      rfl

theorem cell23_3766805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_3766805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766805 prefixEnd_3766805 := by exact prefixLift 3766805
  have htrace : WordTrace (prefixWord ++ tailWord_3766805) baseStart_3766805 baseEnd_3766805 := by
    simpa [prefixWord, tailWord_3766805, baseEnd_3766805] using wordTrace_append hprefix tailTrace_3766805
  have hstable : (prefixWord ++ tailWord_3766805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766805).length < 2 ^ (prefixWord ++ tailWord_3766805).sum := by decide
  have hdescent : baseEnd_3766805 < baseStart_3766805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766816 : List Nat := [2, 1, 1, 6, 2, 2, 1, 1, 2, 3, 2]
def baseStart_3766816 : Nat := 118140960795 + 3766816 * 2 ^ 59
def prefixEnd_3766816 : Nat := 4983230072969 + 3 ^ 40 * 3766816 * 2
def baseEnd_3766816 : Nat := 1934187145046439548776735

theorem tailTrace_3766816 : CollatzResearch.WordTrace tailWord_3766816 prefixEnd_3766816 1934187145046439548776735 := by
  unfold tailWord_3766816
  simp only [CollatzResearch.WordTrace]
  refine ⟨68693533160738213900256151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91591377547650951867008201 68693533160738213900256151)
  ·
    refine ⟨103040299741107320850384227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68693533160738213900256151 103040299741107320850384227)
    ·
      refine ⟨154560449611660981275576341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103040299741107320850384227 154560449611660981275576341)
      ·
        refine ⟨7245021075546608497292641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 154560449611660981275576341 7245021075546608497292641)
        ·
          refine ⟨5433765806659956372969481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7245021075546608497292641 5433765806659956372969481)
          ·
            refine ⟨4075324354994967279727111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5433765806659956372969481 4075324354994967279727111)
            ·
              refine ⟨6112986532492450919590667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4075324354994967279727111 6112986532492450919590667)
              ·
                refine ⟨9169479798738676379386001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6112986532492450919590667 9169479798738676379386001)
                ·
                  refine ⟨6877109849054007284539501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9169479798738676379386001 6877109849054007284539501)
                  ·
                    refine ⟨2578916193395252731702313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6877109849054007284539501 2578916193395252731702313)
                    ·
                      refine ⟨1934187145046439548776735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2578916193395252731702313 1934187145046439548776735)
                      ·
                        rfl

theorem cell23_3766816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_3766816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766816 prefixEnd_3766816 := by exact prefixLift 3766816
  have htrace : WordTrace (prefixWord ++ tailWord_3766816) baseStart_3766816 baseEnd_3766816 := by
    simpa [prefixWord, tailWord_3766816, baseEnd_3766816] using wordTrace_append hprefix tailTrace_3766816
  have hstable : (prefixWord ++ tailWord_3766816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766816).length < 2 ^ (prefixWord ++ tailWord_3766816).sum := by decide
  have hdescent : baseEnd_3766816 < baseStart_3766816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766848 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 1, 9]
def baseStart_3766848 : Nat := 118140960795 + 3766848 * 2 ^ 59
def prefixEnd_3766848 : Nat := 4983230072969 + 3 ^ 40 * 3766848 * 2
def baseEnd_3766848 : Nat := 644734525475794474525529

theorem tailTrace_3766848 : CollatzResearch.WordTrace tailWord_3766848 prefixEnd_3766848 644734525475794474525529 := by
  unfold tailWord_3766848
  simp only [CollatzResearch.WordTrace]
  refine ⟨68694116728680248632838599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91592155638240331510451465 68694116728680248632838599)
  ·
    refine ⟨103041175093020372949257899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68694116728680248632838599 103041175093020372949257899)
    ·
      refine ⟨154561762639530559423886849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103041175093020372949257899 154561762639530559423886849)
      ·
        refine ⟨115921321979647919567915137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154561762639530559423886849 115921321979647919567915137)
        ·
          refine ⟨86940991484735939675936353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115921321979647919567915137 86940991484735939675936353)
          ·
            refine ⟨65205743613551954756952265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86940991484735939675936353 65205743613551954756952265)
            ·
              refine ⟨48904307710163966067714199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65205743613551954756952265 48904307710163966067714199)
              ·
                refine ⟨73356461565245949101571299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48904307710163966067714199 73356461565245949101571299)
                ·
                  refine ⟨110034692347868923652356949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73356461565245949101571299 110034692347868923652356949)
                  ·
                    refine ⟨644734525475794474525529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 110034692347868923652356949 644734525475794474525529)
                    ·
                      rfl

theorem cell23_3766848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 9].length) (baseStart_3766848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766848 prefixEnd_3766848 := by exact prefixLift 3766848
  have htrace : WordTrace (prefixWord ++ tailWord_3766848) baseStart_3766848 baseEnd_3766848 := by
    simpa [prefixWord, tailWord_3766848, baseEnd_3766848] using wordTrace_append hprefix tailTrace_3766848
  have hstable : (prefixWord ++ tailWord_3766848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766848).length < 2 ^ (prefixWord ++ tailWord_3766848).sum := by decide
  have hdescent : baseEnd_3766848 < baseStart_3766848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766862 : List Nat := [4, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3]
def baseStart_3766862 : Nat := 118140960795 + 3766862 * 2 ^ 59
def prefixEnd_3766862 : Nat := 4983230072969 + 3 ^ 40 * 3766862 * 2
def baseEnd_3766862 : Nat := 1934210765156546368801523

theorem tailTrace_3766862 : CollatzResearch.WordTrace tailWord_3766862 prefixEnd_3766862 1934210765156546368801523 := by
  unfold tailWord_3766862
  simp only [CollatzResearch.WordTrace]
  refine ⟨17173593009913722207085855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91592496052873185104457893 17173593009913722207085855)
  ·
    refine ⟨25760389514870583310628783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17173593009913722207085855 25760389514870583310628783)
    ·
      refine ⟨38640584272305874965943175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25760389514870583310628783 38640584272305874965943175)
      ·
        refine ⟨57960876408458812448914763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38640584272305874965943175 57960876408458812448914763)
        ·
          refine ⟨86941314612688218673372145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57960876408458812448914763 86941314612688218673372145)
          ·
            refine ⟨65205985959516164005029109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86941314612688218673372145 65205985959516164005029109)
            ·
              refine ⟨6113061183704640375471479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65205985959516164005029109 6113061183704640375471479)
              ·
                refine ⟨9169591775556960563207219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6113061183704640375471479 9169591775556960563207219)
                ·
                  refine ⟨13754387663335440844810829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9169591775556960563207219 13754387663335440844810829)
                  ·
                    refine ⟨5157895373750790316804061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13754387663335440844810829 5157895373750790316804061)
                    ·
                      refine ⟨1934210765156546368801523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5157895373750790316804061 1934210765156546368801523)
                      ·
                        rfl

theorem cell23_3766862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_3766862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766862 prefixEnd_3766862 := by exact prefixLift 3766862
  have htrace : WordTrace (prefixWord ++ tailWord_3766862) baseStart_3766862 baseEnd_3766862 := by
    simpa [prefixWord, tailWord_3766862, baseEnd_3766862] using wordTrace_append hprefix tailTrace_3766862
  have hstable : (prefixWord ++ tailWord_3766862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766862).length < 2 ^ (prefixWord ++ tailWord_3766862).sum := by decide
  have hdescent : baseEnd_3766862 < baseStart_3766862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766872 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 3, 3, 2]
def baseStart_3766872 : Nat := 118140960795 + 3766872 * 2 ^ 59
def prefixEnd_3766872 : Nat := 4983230072969 + 3 ^ 40 * 3766872 * 2
def baseEnd_3766872 : Nat := 1934215899963091329676477

theorem tailTrace_3766872 : CollatzResearch.WordTrace tailWord_3766872 prefixEnd_3766872 1934215899963091329676477 := by
  unfold tailWord_3766872
  simp only [CollatzResearch.WordTrace]
  refine ⟨68694554404636774682275435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91592739206182366243033913 68694554404636774682275435)
  ·
    refine ⟨103041831606955162023413153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68694554404636774682275435 103041831606955162023413153)
    ·
      refine ⟨77281373705216371517559865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103041831606955162023413153 77281373705216371517559865)
      ·
        refine ⟨57961030278912278638169899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77281373705216371517559865 57961030278912278638169899)
        ·
          refine ⟨86941545418368417957254849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57961030278912278638169899 86941545418368417957254849)
          ·
            refine ⟨65206159063776313467941137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86941545418368417957254849 65206159063776313467941137)
            ·
              refine ⟨48904619297832235100955853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65206159063776313467941137 48904619297832235100955853)
              ·
                refine ⟨18339232236687088162858445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48904619297832235100955853 18339232236687088162858445)
                ·
                  refine ⟨6877212088757658061071917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18339232236687088162858445 6877212088757658061071917)
                  ·
                    refine ⟨2578954533284121772901969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6877212088757658061071917 2578954533284121772901969)
                    ·
                      refine ⟨1934215899963091329676477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2578954533284121772901969 1934215899963091329676477)
                      ·
                        rfl

theorem cell23_3766872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_3766872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766872 prefixEnd_3766872 := by exact prefixLift 3766872
  have htrace : WordTrace (prefixWord ++ tailWord_3766872) baseStart_3766872 baseEnd_3766872 := by
    simpa [prefixWord, tailWord_3766872, baseEnd_3766872] using wordTrace_append hprefix tailTrace_3766872
  have hstable : (prefixWord ++ tailWord_3766872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766872).length < 2 ^ (prefixWord ++ tailWord_3766872).sum := by decide
  have hdescent : baseEnd_3766872 < baseStart_3766872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766915 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 4]
def baseStart_3766915 : Nat := 118140960795 + 3766915 * 2 ^ 59
def prefixEnd_3766915 : Nat := 4983230072969 + 3 ^ 40 * 3766915 * 2
def baseEnd_3766915 : Nat := 1934237979631234661438779

theorem tailTrace_3766915 : CollatzResearch.WordTrace tailWord_3766915 prefixEnd_3766915 1934237979631234661438779 := by
  unfold tailWord_3766915
  simp only [CollatzResearch.WordTrace]
  refine ⟨137390677148117767708366199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91593784765411845138910799 137390677148117767708366199)
  ·
    refine ⟨206086015722176651562549299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137390677148117767708366199 206086015722176651562549299)
    ·
      refine ⟨309129023583264977343823949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206086015722176651562549299 309129023583264977343823949)
      ·
        refine ⟨115923383843724366503933981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309129023583264977343823949 115923383843724366503933981)
        ·
          refine ⟨43471268941396637438975243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115923383843724366503933981 43471268941396637438975243)
          ·
            refine ⟨65206903412094956158462865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43471268941396637438975243 65206903412094956158462865)
            ·
              refine ⟨48905177559071217118847149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65206903412094956158462865 48905177559071217118847149)
              ·
                refine ⟨18339441584651706419567681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48905177559071217118847149 18339441584651706419567681)
                ·
                  refine ⟨13754581188488779814675761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18339441584651706419567681 13754581188488779814675761)
                  ·
                    refine ⟨10315935891366584861006821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13754581188488779814675761 10315935891366584861006821)
                    ·
                      refine ⟨1934237979631234661438779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10315935891366584861006821 1934237979631234661438779)
                      ·
                        rfl

theorem cell23_3766915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_3766915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766915 prefixEnd_3766915 := by exact prefixLift 3766915
  have htrace : WordTrace (prefixWord ++ tailWord_3766915) baseStart_3766915 baseEnd_3766915 := by
    simpa [prefixWord, tailWord_3766915, baseEnd_3766915] using wordTrace_append hprefix tailTrace_3766915
  have hstable : (prefixWord ++ tailWord_3766915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766915).length < 2 ^ (prefixWord ++ tailWord_3766915).sum := by decide
  have hdescent : baseEnd_3766915 < baseStart_3766915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766959 : List Nat := [1, 1, 2, 1, 2, 5, 4, 2, 5]
def baseStart_3766959 : Nat := 118140960795 + 3766959 * 2 ^ 59
def prefixEnd_3766959 : Nat := 4983230072969 + 3 ^ 40 * 3766959 * 2
def baseEnd_3766959 : Nat := 214917841420003609920953

theorem tailTrace_3766959 : CollatzResearch.WordTrace tailWord_3766959 prefixEnd_3766959 214917841420003609920953 := by
  unfold tailWord_3766959
  simp only [CollatzResearch.WordTrace]
  refine ⟨137392281959958363222967931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91594854639972242148645287 137392281959958363222967931)
  ·
    refine ⟨206088422939937544834451897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137392281959958363222967931 206088422939937544834451897)
    ·
      refine ⟨154566317204953158625838923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206088422939937544834451897 154566317204953158625838923)
      ·
        refine ⟨231849475807429737938758385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154566317204953158625838923 231849475807429737938758385)
        ·
          refine ⟨173887106855572303454068789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231849475807429737938758385 173887106855572303454068789)
          ·
            refine ⟨16301916267709903448818949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173887106855572303454068789 16301916267709903448818949)
            ·
              refine ⟨3056609300195606896653553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16301916267709903448818949 3056609300195606896653553)
              ·
                refine ⟨2292456975146705172490165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3056609300195606896653553 2292456975146705172490165)
                ·
                  refine ⟨214917841420003609920953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2292456975146705172490165 214917841420003609920953)
                  ·
                    rfl

theorem cell23_3766959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 5].length) (baseStart_3766959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766959 prefixEnd_3766959 := by exact prefixLift 3766959
  have htrace : WordTrace (prefixWord ++ tailWord_3766959) baseStart_3766959 baseEnd_3766959 := by
    simpa [prefixWord, tailWord_3766959, baseEnd_3766959] using wordTrace_append hprefix tailTrace_3766959
  have hstable : (prefixWord ++ tailWord_3766959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766959).length < 2 ^ (prefixWord ++ tailWord_3766959).sum := by decide
  have hdescent : baseEnd_3766959 < baseStart_3766959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766966 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_3766966 : Nat := 118140960795 + 3766966 * 2 ^ 59
def prefixEnd_3766966 : Nat := 4983230072969 + 3 ^ 40 * 3766966 * 2
def baseEnd_3766966 : Nat := 1934264167144613961901045

theorem tailTrace_3766966 : CollatzResearch.WordTrace tailWord_3766966 prefixEnd_3766966 1934264167144613961901045 := by
  unfold tailWord_3766966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8587033579433312713654547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91595024847288668945648501 8587033579433312713654547)
  ·
    refine ⟨12880550369149969070481821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8587033579433312713654547 12880550369149969070481821)
    ·
      refine ⟨4830206388431238401430683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12880550369149969070481821 4830206388431238401430683)
      ·
        refine ⟨7245309582646857602146025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4830206388431238401430683 7245309582646857602146025)
        ·
          refine ⟨5433982186985143201609519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7245309582646857602146025 5433982186985143201609519)
          ·
            refine ⟨8150973280477714802414279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5433982186985143201609519 8150973280477714802414279)
            ·
              refine ⟨12226459920716572203621419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8150973280477714802414279 12226459920716572203621419)
              ·
                refine ⟨18339689881074858305432129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12226459920716572203621419 18339689881074858305432129)
                ·
                  refine ⟨13754767410806143729074097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18339689881074858305432129 13754767410806143729074097)
                  ·
                    refine ⟨10316075558104607796805573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13754767410806143729074097 10316075558104607796805573)
                    ·
                      refine ⟨1934264167144613961901045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10316075558104607796805573 1934264167144613961901045)
                      ·
                        rfl

theorem cell23_3766966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_3766966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766966 prefixEnd_3766966 := by exact prefixLift 3766966
  have htrace : WordTrace (prefixWord ++ tailWord_3766966) baseStart_3766966 baseEnd_3766966 := by
    simpa [prefixWord, tailWord_3766966, baseEnd_3766966] using wordTrace_append hprefix tailTrace_3766966
  have hstable : (prefixWord ++ tailWord_3766966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766966).length < 2 ^ (prefixWord ++ tailWord_3766966).sum := by decide
  have hdescent : baseEnd_3766966 < baseStart_3766966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767002 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 5, 4]
def baseStart_3767002 : Nat := 118140960795 + 3767002 * 2 ^ 59
def prefixEnd_3767002 : Nat := 4983230072969 + 3 ^ 40 * 3767002 * 2
def baseEnd_3767002 : Nat := 644760884149391940350293

theorem tailTrace_3767002 : CollatzResearch.WordTrace tailWord_3767002 prefixEnd_3767002 644760884149391940350293 := by
  unfold tailWord_3767002
  simp only [CollatzResearch.WordTrace]
  refine ⟨34348462574700645391695815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91595900199201721044522173 34348462574700645391695815)
  ·
    refine ⟨51522693862050968087543723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34348462574700645391695815 51522693862050968087543723)
    ·
      refine ⟨77284040793076452131315585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51522693862050968087543723 77284040793076452131315585)
      ·
        refine ⟨57963030594807339098486689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77284040793076452131315585 57963030594807339098486689)
        ·
          refine ⟨43472272946105504323865017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57963030594807339098486689 43472272946105504323865017)
          ·
            refine ⟨32604204709579128242898763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43472272946105504323865017 32604204709579128242898763)
            ·
              refine ⟨48906307064368692364348145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32604204709579128242898763 48906307064368692364348145)
              ·
                refine ⟨36679730298276519273261109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48906307064368692364348145 36679730298276519273261109)
                ·
                  refine ⟨3438724715463423681868229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36679730298276519273261109 3438724715463423681868229)
                  ·
                    refine ⟨644760884149391940350293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3438724715463423681868229 644760884149391940350293)
                    ·
                      rfl

theorem cell23_3767002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_3767002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767002 prefixEnd_3767002 := by exact prefixLift 3767002
  have htrace : WordTrace (prefixWord ++ tailWord_3767002) baseStart_3767002 baseEnd_3767002 := by
    simpa [prefixWord, tailWord_3767002, baseEnd_3767002] using wordTrace_append hprefix tailTrace_3767002
  have hstable : (prefixWord ++ tailWord_3767002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767002).length < 2 ^ (prefixWord ++ tailWord_3767002).sum := by decide
  have hdescent : baseEnd_3767002 < baseStart_3767002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767009 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 2, 4, 2]
def baseStart_3767009 : Nat := 118140960795 + 3767009 * 2 ^ 59
def prefixEnd_3767009 : Nat := 4983230072969 + 3 ^ 40 * 3767009 * 2
def baseEnd_3767009 : Nat := 1934286246812757293663347

theorem tailTrace_3767009 : CollatzResearch.WordTrace tailWord_3767009 prefixEnd_3767009 1934286246812757293663347 := by
  unfold tailWord_3767009
  simp only [CollatzResearch.WordTrace]
  refine ⟨137394105609777221762288081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91596070406518147841525387 137394105609777221762288081)
  ·
    refine ⟨103045579207332916321716061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137394105609777221762288081 103045579207332916321716061)
    ·
      refine ⟨38642092202749843620643523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103045579207332916321716061 38642092202749843620643523)
      ·
        refine ⟨57963138304124765430965285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38642092202749843620643523 57963138304124765430965285)
        ·
          refine ⟨10868088432023393518305991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57963138304124765430965285 10868088432023393518305991)
          ·
            refine ⟨16302132648035090277458987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10868088432023393518305991 16302132648035090277458987)
            ·
              refine ⟨24453198972052635416188481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16302132648035090277458987 24453198972052635416188481)
              ·
                refine ⟨18339899229039476562141361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24453198972052635416188481 18339899229039476562141361)
                ·
                  refine ⟨13754924421779607421606021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18339899229039476562141361 13754924421779607421606021)
                  ·
                    refine ⟨2579048329083676391551129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13754924421779607421606021 2579048329083676391551129)
                    ·
                      refine ⟨1934286246812757293663347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2579048329083676391551129 1934286246812757293663347)
                      ·
                        rfl

theorem cell23_3767009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_3767009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767009 prefixEnd_3767009 := by exact prefixLift 3767009
  have htrace : WordTrace (prefixWord ++ tailWord_3767009) baseStart_3767009 baseEnd_3767009 := by
    simpa [prefixWord, tailWord_3767009, baseEnd_3767009] using wordTrace_append hprefix tailTrace_3767009
  have hstable : (prefixWord ++ tailWord_3767009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767009).length < 2 ^ (prefixWord ++ tailWord_3767009).sum := by decide
  have hdescent : baseEnd_3767009 < baseStart_3767009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767045 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 2, 9]
def baseStart_3767045 : Nat := 118140960795 + 3767045 * 2 ^ 59
def prefixEnd_3767045 : Nat := 4983230072969 + 3 ^ 40 * 3767045 * 2
def baseEnd_3767045 : Nat := 644768244038773050937727

theorem tailTrace_3767045 : CollatzResearch.WordTrace tailWord_3767045 prefixEnd_3767045 644768244038773050937727 := by
  unfold tailWord_3767045
  simp only [CollatzResearch.WordTrace]
  refine ⟨137395418637646799910598589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91596945758431199940399059 137395418637646799910598589)
  ·
    refine ⟨51523281989117549966474471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137395418637646799910598589 51523281989117549966474471)
    ·
      refine ⟨77284922983676324949711707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51523281989117549966474471 77284922983676324949711707)
      ·
        refine ⟨115927384475514487424567561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77284922983676324949711707 115927384475514487424567561)
        ·
          refine ⟨86945538356635865568425671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115927384475514487424567561 86945538356635865568425671)
          ·
            refine ⟨130418307534953798352638507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86945538356635865568425671 130418307534953798352638507)
            ·
              refine ⟨195627461302430697528957761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130418307534953798352638507 195627461302430697528957761)
              ·
                refine ⟨146720595976823023146718321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195627461302430697528957761 146720595976823023146718321)
                ·
                  refine ⟨110040446982617267360038741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146720595976823023146718321 110040446982617267360038741)
                  ·
                    refine ⟨644768244038773050937727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 110040446982617267360038741 644768244038773050937727)
                    ·
                      rfl

theorem cell23_3767045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_3767045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767045 prefixEnd_3767045 := by exact prefixLift 3767045
  have htrace : WordTrace (prefixWord ++ tailWord_3767045) baseStart_3767045 baseEnd_3767045 := by
    simpa [prefixWord, tailWord_3767045, baseEnd_3767045] using wordTrace_append hprefix tailTrace_3767045
  have hstable : (prefixWord ++ tailWord_3767045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767045).length < 2 ^ (prefixWord ++ tailWord_3767045).sum := by decide
  have hdescent : baseEnd_3767045 < baseStart_3767045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767139 : List Nat := [1, 1, 1, 5, 3, 3, 1, 8]
def baseStart_3767139 : Nat := 118140960795 + 3767139 * 2 ^ 59
def prefixEnd_3767139 : Nat := 4983230072969 + 3 ^ 40 * 3767139 * 2
def baseEnd_3767139 : Nat := 71642703677697843890287

theorem tailTrace_3767139 : CollatzResearch.WordTrace tailWord_3767139 prefixEnd_3767139 71642703677697843890287 := by
  unfold tailWord_3767139
  simp only [CollatzResearch.WordTrace]
  refine ⟨137398847099306253964520471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91599231399537502643013647 137398847099306253964520471)
  ·
    refine ⟨206098270648959380946780707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137398847099306253964520471 206098270648959380946780707)
    ·
      refine ⟨309147405973439071420171061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206098270648959380946780707 309147405973439071420171061)
      ·
        refine ⟨28982569310009912945641037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 309147405973439071420171061 28982569310009912945641037)
        ·
          refine ⟨10868463491253717354615389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28982569310009912945641037 10868463491253717354615389)
          ·
            refine ⟨4075673809220144007980771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10868463491253717354615389 4075673809220144007980771)
            ·
              refine ⟨6113510713830216011971157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4075673809220144007980771 6113510713830216011971157)
              ·
                refine ⟨71642703677697843890287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6113510713830216011971157 71642703677697843890287)
                ·
                  rfl

theorem cell23_3767139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 8].length) (baseStart_3767139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767139 prefixEnd_3767139 := by exact prefixLift 3767139
  have htrace : WordTrace (prefixWord ++ tailWord_3767139) baseStart_3767139 baseEnd_3767139 := by
    simpa [prefixWord, tailWord_3767139, baseEnd_3767139] using wordTrace_append hprefix tailTrace_3767139
  have hstable : (prefixWord ++ tailWord_3767139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767139).length < 2 ^ (prefixWord ++ tailWord_3767139).sum := by decide
  have hdescent : baseEnd_3767139 < baseStart_3767139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767150 : List Nat := [4, 1, 2, 3, 2, 1, 1, 2, 3, 2, 2]
def baseStart_3767150 : Nat := 118140960795 + 3767150 * 2 ^ 59
def prefixEnd_3767150 : Nat := 4983230072969 + 3 ^ 40 * 3767150 * 2
def baseEnd_3767150 : Nat := 1934358647585041242000199

theorem tailTrace_3767150 : CollatzResearch.WordTrace tailWord_3767150 prefixEnd_3767150 1934358647585041242000199 := by
  unfold tailWord_3767150
  simp only [CollatzResearch.WordTrace]
  refine ⟨17174906037783300355396363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91599498868177601895447269 17174906037783300355396363)
  ·
    refine ⟨25762359056674950533094545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17174906037783300355396363 25762359056674950533094545)
    ·
      refine ⟨19321769292506212899820909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25762359056674950533094545 19321769292506212899820909)
      ·
        refine ⟨7245663484689829837432841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19321769292506212899820909 7245663484689829837432841)
        ·
          refine ⟨5434247613517372378074631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7245663484689829837432841 5434247613517372378074631)
          ·
            refine ⟨8151371420276058567111947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5434247613517372378074631 8151371420276058567111947)
            ·
              refine ⟨12227057130414087850667921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8151371420276058567111947 12227057130414087850667921)
              ·
                refine ⟨9170292847810565888000941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12227057130414087850667921 9170292847810565888000941)
                ·
                  refine ⟨3438859817928962208000353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9170292847810565888000941 3438859817928962208000353)
                  ·
                    refine ⟨2579144863446721656000265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3438859817928962208000353 2579144863446721656000265)
                    ·
                      refine ⟨1934358647585041242000199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2579144863446721656000265 1934358647585041242000199)
                      ·
                        rfl

theorem cell23_3767150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_3767150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767150 prefixEnd_3767150 := by exact prefixLift 3767150
  have htrace : WordTrace (prefixWord ++ tailWord_3767150) baseStart_3767150 baseEnd_3767150 := by
    simpa [prefixWord, tailWord_3767150, baseEnd_3767150] using wordTrace_append hprefix tailTrace_3767150
  have hstable : (prefixWord ++ tailWord_3767150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767150).length < 2 ^ (prefixWord ++ tailWord_3767150).sum := by decide
  have hdescent : baseEnd_3767150 < baseStart_3767150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767162 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5]
def baseStart_3767162 : Nat := 118140960795 + 3767162 * 2 ^ 59
def prefixEnd_3767162 : Nat := 4983230072969 + 3 ^ 40 * 3767162 * 2
def baseEnd_3767162 : Nat := 1934364809352895195050143

theorem tailTrace_3767162 : CollatzResearch.WordTrace tailWord_3767162 prefixEnd_3767162 1934364809352895195050143 := by
  unfold tailWord_3767162
  simp only [CollatzResearch.WordTrace]
  refine ⟨34349921494555732223151935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91599790652148619261738493 34349921494555732223151935)
  ·
    refine ⟨51524882241833598334727903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34349921494555732223151935 51524882241833598334727903)
    ·
      refine ⟨77287323362750397502091855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51524882241833598334727903 77287323362750397502091855)
      ·
        refine ⟨115930985044125596253137783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77287323362750397502091855 115930985044125596253137783)
        ·
          refine ⟨173896477566188394379706675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115930985044125596253137783 173896477566188394379706675)
          ·
            refine ⟨260844716349282591569560013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173896477566188394379706675 260844716349282591569560013)
            ·
              refine ⟨97816768630980971838585005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260844716349282591569560013 97816768630980971838585005)
              ·
                refine ⟨36681288236617864439469377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97816768630980971838585005 36681288236617864439469377)
                ·
                  refine ⟨27510966177463398329602033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36681288236617864439469377 27510966177463398329602033)
                  ·
                    refine ⟨20633224633097548747201525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27510966177463398329602033 20633224633097548747201525)
                    ·
                      refine ⟨1934364809352895195050143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20633224633097548747201525 1934364809352895195050143)
                      ·
                        rfl

theorem cell23_3767162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_3767162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767162 prefixEnd_3767162 := by exact prefixLift 3767162
  have htrace : WordTrace (prefixWord ++ tailWord_3767162) baseStart_3767162 baseEnd_3767162 := by
    simpa [prefixWord, tailWord_3767162, baseEnd_3767162] using wordTrace_append hprefix tailTrace_3767162
  have hstable : (prefixWord ++ tailWord_3767162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767162).length < 2 ^ (prefixWord ++ tailWord_3767162).sum := by decide
  have hdescent : baseEnd_3767162 < baseStart_3767162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767199 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 2, 6]
def baseStart_3767199 : Nat := 118140960795 + 3767199 * 2 ^ 59
def prefixEnd_3767199 : Nat := 4983230072969 + 3 ^ 40 * 3767199 * 2
def baseEnd_3767199 : Nat := 644794602712370516762491

theorem tailTrace_3767199 : CollatzResearch.WordTrace tailWord_3767199 prefixEnd_3767199 644794602712370516762491 := by
  unfold tailWord_3767199
  simp only [CollatzResearch.WordTrace]
  refine ⟨137401035479088884211704651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91600690319392589474469767 137401035479088884211704651)
  ·
    refine ⟨206101553218633326317556977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137401035479088884211704651 206101553218633326317556977)
    ·
      refine ⟨154576164913974994738167733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206101553218633326317556977 154576164913974994738167733)
      ·
        refine ⟨14491515460685155756703225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154576164913974994738167733 14491515460685155756703225)
        ·
          refine ⟨10868636595513866817527419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14491515460685155756703225 10868636595513866817527419)
          ·
            refine ⟨16302954893270800226291129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10868636595513866817527419 16302954893270800226291129)
            ·
              refine ⟨12227216169953100169718347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16302954893270800226291129 12227216169953100169718347)
              ·
                refine ⟨18340824254929650254577521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12227216169953100169718347 18340824254929650254577521)
                ·
                  refine ⟨13755618191197237690933141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18340824254929650254577521 13755618191197237690933141)
                  ·
                    refine ⟨644794602712370516762491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13755618191197237690933141 644794602712370516762491)
                    ·
                      rfl

theorem cell23_3767199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 6].length) (baseStart_3767199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767199 prefixEnd_3767199 := by exact prefixLift 3767199
  have htrace : WordTrace (prefixWord ++ tailWord_3767199) baseStart_3767199 baseEnd_3767199 := by
    simpa [prefixWord, tailWord_3767199, baseEnd_3767199] using wordTrace_append hprefix tailTrace_3767199
  have hstable : (prefixWord ++ tailWord_3767199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767199).length < 2 ^ (prefixWord ++ tailWord_3767199).sum := by decide
  have hdescent : baseEnd_3767199 < baseStart_3767199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767239 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 3]
def baseStart_3767239 : Nat := 118140960795 + 3767239 * 2 ^ 59
def prefixEnd_3767239 : Nat := 4983230072969 + 3 ^ 40 * 3767239 * 2
def baseEnd_3767239 : Nat := 1934404347363291393787289

theorem tailTrace_3767239 : CollatzResearch.WordTrace tailWord_3767239 prefixEnd_3767239 1934404347363291393787289 := by
  unfold tailWord_3767239
  simp only [CollatzResearch.WordTrace]
  refine ⟨137402494398943971043160771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91601662932629314028773847 137402494398943971043160771)
  ·
    refine ⟨206103741598415956564741157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137402494398943971043160771 206103741598415956564741157)
    ·
      refine ⟨38644451549702991855888967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206103741598415956564741157 38644451549702991855888967)
      ·
        refine ⟨57966677324554487783833451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38644451549702991855888967 57966677324554487783833451)
        ·
          refine ⟨86950015986831731675750177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57966677324554487783833451 86950015986831731675750177)
          ·
            refine ⟨65212511990123798756812633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86950015986831731675750177 65212511990123798756812633)
            ·
              refine ⟨48909383992592849067609475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65212511990123798756812633 48909383992592849067609475)
              ·
                refine ⟨73364075988889273601414213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48909383992592849067609475 73364075988889273601414213)
                ·
                  refine ⟨13755764247916738800265165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73364075988889273601414213 13755764247916738800265165)
                  ·
                    refine ⟨5158411592968777050099437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13755764247916738800265165 5158411592968777050099437)
                    ·
                      refine ⟨1934404347363291393787289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5158411592968777050099437 1934404347363291393787289)
                      ·
                        rfl

theorem cell23_3767239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_3767239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767239 prefixEnd_3767239 := by exact prefixLift 3767239
  have htrace : WordTrace (prefixWord ++ tailWord_3767239) baseStart_3767239 baseEnd_3767239 := by
    simpa [prefixWord, tailWord_3767239, baseEnd_3767239] using wordTrace_append hprefix tailTrace_3767239
  have hstable : (prefixWord ++ tailWord_3767239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767239).length < 2 ^ (prefixWord ++ tailWord_3767239).sum := by decide
  have hdescent : baseEnd_3767239 < baseStart_3767239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767246 : List Nat := [4, 1, 1, 1, 2, 5, 1, 1, 7]
def baseStart_3767246 : Nat := 118140960795 + 3767246 * 2 ^ 59
def prefixEnd_3767246 : Nat := 4983230072969 + 3 ^ 40 * 3767246 * 2
def baseEnd_3767246 : Nat := 214934215747541429599973

theorem tailTrace_3767246 : CollatzResearch.WordTrace tailWord_3767246 prefixEnd_3767246 214934215747541429599973 := by
  unfold tailWord_3767246
  simp only [CollatzResearch.WordTrace]
  refine ⟨17175343713739826404833199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91601833139945740825777061 17175343713739826404833199)
  ·
    refine ⟨25763015570609739607249799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17175343713739826404833199 25763015570609739607249799)
    ·
      refine ⟨38644523355914609410874699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25763015570609739607249799 38644523355914609410874699)
      ·
        refine ⟨57966785033871914116312049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38644523355914609410874699 57966785033871914116312049)
        ·
          refine ⟨43475088775403935587234037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57966785033871914116312049 43475088775403935587234037)
          ·
            refine ⟨4075789572694118961303191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43475088775403935587234037 4075789572694118961303191)
            ·
              refine ⟨6113684359041178441954787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4075789572694118961303191 6113684359041178441954787)
              ·
                refine ⟨9170526538561767662932181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6113684359041178441954787 9170526538561767662932181)
                ·
                  refine ⟨214934215747541429599973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9170526538561767662932181 214934215747541429599973)
                  ·
                    rfl

theorem cell23_3767246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_3767246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767246 prefixEnd_3767246 := by exact prefixLift 3767246
  have htrace : WordTrace (prefixWord ++ tailWord_3767246) baseStart_3767246 baseEnd_3767246 := by
    simpa [prefixWord, tailWord_3767246, baseEnd_3767246] using wordTrace_append hprefix tailTrace_3767246
  have hstable : (prefixWord ++ tailWord_3767246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767246).length < 2 ^ (prefixWord ++ tailWord_3767246).sum := by decide
  have hdescent : baseEnd_3767246 < baseStart_3767246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767257 : List Nat := [1, 2, 1, 2, 5, 3, 2, 1, 2, 2, 2]
def baseStart_3767257 : Nat := 118140960795 + 3767257 * 2 ^ 59
def prefixEnd_3767257 : Nat := 4983230072969 + 3 ^ 40 * 3767257 * 2
def baseEnd_3767257 : Nat := 1934413590015072323362207

theorem tailTrace_3767257 : CollatzResearch.WordTrace tailWord_3767257 prefixEnd_3767257 1934413590015072323362207 := by
  unfold tailWord_3767257
  simp only [CollatzResearch.WordTrace]
  refine ⟨137403150912878760117316025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91602100608585840078210683 137403150912878760117316025)
  ·
    refine ⟨103052363184659070087987019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137403150912878760117316025 103052363184659070087987019)
    ·
      refine ⟨154578544776988605131980529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103052363184659070087987019 154578544776988605131980529)
      ·
        refine ⟨115933908582741453848985397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154578544776988605131980529 115933908582741453848985397)
        ·
          refine ⟨10868803929632011298342381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115933908582741453848985397 10868803929632011298342381)
          ·
            refine ⟨4075801473612004236878393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10868803929632011298342381 4075801473612004236878393)
            ·
              refine ⟨3056851105209003177658795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4075801473612004236878393 3056851105209003177658795)
              ·
                refine ⟨4585276657813504766488193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3056851105209003177658795 4585276657813504766488193)
                ·
                  refine ⟨3438957493360128574866145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4585276657813504766488193 3438957493360128574866145)
                  ·
                    refine ⟨2579218120020096431149609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3438957493360128574866145 2579218120020096431149609)
                    ·
                      refine ⟨1934413590015072323362207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2579218120020096431149609 1934413590015072323362207)
                      ·
                        rfl

theorem cell23_3767257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 2, 2, 2].length) (baseStart_3767257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767257 prefixEnd_3767257 := by exact prefixLift 3767257
  have htrace : WordTrace (prefixWord ++ tailWord_3767257) baseStart_3767257 baseEnd_3767257 := by
    simpa [prefixWord, tailWord_3767257, baseEnd_3767257] using wordTrace_append hprefix tailTrace_3767257
  have hstable : (prefixWord ++ tailWord_3767257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767257).length < 2 ^ (prefixWord ++ tailWord_3767257).sum := by decide
  have hdescent : baseEnd_3767257 < baseStart_3767257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767286 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_3767286 : Nat := 118140960795 + 3767286 * 2 ^ 59
def prefixEnd_3767286 : Nat := 4983230072969 + 3 ^ 40 * 3767286 * 2
def baseEnd_3767286 : Nat := 1934428480954052709899573

theorem tailTrace_3767286 : CollatzResearch.WordTrace tailWord_3767286 prefixEnd_3767286 1934428480954052709899573 := by
  unfold tailWord_3767286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8587763039360856129382607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91602805753182465380081141 8587763039360856129382607)
  ·
    refine ⟨12881644559041284194073911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8587763039360856129382607 12881644559041284194073911)
    ·
      refine ⟨19322466838561926291110867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12881644559041284194073911 19322466838561926291110867)
      ·
        refine ⟨28983700257842889436666301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19322466838561926291110867 28983700257842889436666301)
        ·
          refine ⟨10868887596691083538749863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28983700257842889436666301 10868887596691083538749863)
          ·
            refine ⟨16303331395036625308124795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10868887596691083538749863 16303331395036625308124795)
            ·
              refine ⟨24454997092554937962187193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16303331395036625308124795 24454997092554937962187193)
              ·
                refine ⟨18341247819416203471640395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24454997092554937962187193 18341247819416203471640395)
                ·
                  refine ⟨27511871729124305207460593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18341247819416203471640395 27511871729124305207460593)
                  ·
                    refine ⟨20633903796843228905595445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27511871729124305207460593 20633903796843228905595445)
                    ·
                      refine ⟨1934428480954052709899573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20633903796843228905595445 1934428480954052709899573)
                      ·
                        rfl

theorem cell23_3767286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_3767286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767286 prefixEnd_3767286 := by exact prefixLift 3767286
  have htrace : WordTrace (prefixWord ++ tailWord_3767286) baseStart_3767286 baseEnd_3767286 := by
    simpa [prefixWord, tailWord_3767286, baseEnd_3767286] using wordTrace_append hprefix tailTrace_3767286
  have hstable : (prefixWord ++ tailWord_3767286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767286).length < 2 ^ (prefixWord ++ tailWord_3767286).sum := by decide
  have hdescent : baseEnd_3767286 < baseStart_3767286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767299 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 3]
def baseStart_3767299 : Nat := 118140960795 + 3767299 * 2 ^ 59
def prefixEnd_3767299 : Nat := 4983230072969 + 3 ^ 40 * 3767299 * 2
def baseEnd_3767299 : Nat := 1934435156202561159037013

theorem tailTrace_3767299 : CollatzResearch.WordTrace tailWord_3767299 prefixEnd_3767299 1934435156202561159037013 := by
  unfold tailWord_3767299
  simp only [CollatzResearch.WordTrace]
  refine ⟨137404682778726601290344951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91603121852484400860229967 137404682778726601290344951)
  ·
    refine ⟨206107024168089901935517427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137404682778726601290344951 206107024168089901935517427)
    ·
      refine ⟨309160536252134852903276141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206107024168089901935517427 309160536252134852903276141)
      ·
        refine ⟨115935201094550569838728553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309160536252134852903276141 115935201094550569838728553)
        ·
          refine ⟨86951400820912927379046415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115935201094550569838728553 86951400820912927379046415)
          ·
            refine ⟨130427101231369391068569623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86951400820912927379046415 130427101231369391068569623)
            ·
              refine ⟨195640651847054086602854435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130427101231369391068569623 195640651847054086602854435)
              ·
                refine ⟨293460977770581129904281653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195640651847054086602854435 293460977770581129904281653)
                ·
                  refine ⟨27511966665991980928526405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 293460977770581129904281653 27511966665991980928526405)
                  ·
                    refine ⟨5158493749873496424098701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27511966665991980928526405 5158493749873496424098701)
                    ·
                      refine ⟨1934435156202561159037013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5158493749873496424098701 1934435156202561159037013)
                      ·
                        rfl

theorem cell23_3767299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_3767299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767299 prefixEnd_3767299 := by exact prefixLift 3767299
  have htrace : WordTrace (prefixWord ++ tailWord_3767299) baseStart_3767299 baseEnd_3767299 := by
    simpa [prefixWord, tailWord_3767299, baseEnd_3767299] using wordTrace_append hprefix tailTrace_3767299
  have hstable : (prefixWord ++ tailWord_3767299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767299).length < 2 ^ (prefixWord ++ tailWord_3767299).sum := by decide
  have hdescent : baseEnd_3767299 < baseStart_3767299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767353 : List Nat := [1, 2, 1, 5, 2, 3, 1, 2, 6]
def baseStart_3767353 : Nat := 118140960795 + 3767353 * 2 ^ 59
def prefixEnd_3767353 : Nat := 4983230072969 + 3 ^ 40 * 3767353 * 2
def baseEnd_3767353 : Nat := 214940320461989327529085

theorem tailTrace_3767353 : CollatzResearch.WordTrace tailWord_3767353 prefixEnd_3767353 214940320461989327529085 := by
  unfold tailWord_3767353
  simp only [CollatzResearch.WordTrace]
  refine ⟨137406652320530968512810713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91604434880353979008540475 137406652320530968512810713)
  ·
    refine ⟨103054989240398226384608035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137406652320530968512810713 103054989240398226384608035)
    ·
      refine ⟨154582483860597339576912053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103054989240398226384608035 154582483860597339576912053)
      ·
        refine ⟨14492107861931000585335505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154582483860597339576912053 14492107861931000585335505)
        ·
          refine ⟨10869080896448250439001629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14492107861931000585335505 10869080896448250439001629)
          ·
            refine ⟨4075905336168093914625611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10869080896448250439001629 4075905336168093914625611)
            ·
              refine ⟨6113858004252140871938417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4075905336168093914625611 6113858004252140871938417)
              ·
                refine ⟨4585393503189105653953813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6113858004252140871938417 4585393503189105653953813)
                ·
                  refine ⟨214940320461989327529085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4585393503189105653953813 214940320461989327529085)
                  ·
                    rfl

theorem cell23_3767353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 6].length) (baseStart_3767353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767353 prefixEnd_3767353 := by exact prefixLift 3767353
  have htrace : WordTrace (prefixWord ++ tailWord_3767353) baseStart_3767353 baseEnd_3767353 := by
    simpa [prefixWord, tailWord_3767353, baseEnd_3767353] using wordTrace_append hprefix tailTrace_3767353
  have hstable : (prefixWord ++ tailWord_3767353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767353).length < 2 ^ (prefixWord ++ tailWord_3767353).sum := by decide
  have hdescent : baseEnd_3767353 < baseStart_3767353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767363 : List Nat := [1, 1, 1, 3, 1, 2, 6, 1, 3, 1, 3]
def baseStart_3767363 : Nat := 118140960795 + 3767363 * 2 ^ 59
def prefixEnd_3767363 : Nat := 4983230072969 + 3 ^ 40 * 3767363 * 2
def baseEnd_3767363 : Nat := 1934468018964448908636719

theorem tailTrace_3767363 : CollatzResearch.WordTrace tailWord_3767363 prefixEnd_3767363 1934468018964448908636719 := by
  unfold tailWord_3767363
  simp only [CollatzResearch.WordTrace]
  refine ⟨137407017050494740220674743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91604678033663160147116495 137407017050494740220674743)
  ·
    refine ⟨206110525575742110331012115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137407017050494740220674743 206110525575742110331012115)
    ·
      refine ⟨309165788363613165496518173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206110525575742110331012115 309165788363613165496518173)
      ·
        refine ⟨115937170636354937061194315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309165788363613165496518173 115937170636354937061194315)
        ·
          refine ⟨173905755954532405591791473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115937170636354937061194315 173905755954532405591791473)
          ·
            refine ⟨130429316965899304193843605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173905755954532405591791473 130429316965899304193843605)
            ·
              refine ⟨6113874232776529884086419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130429316965899304193843605 6113874232776529884086419)
              ·
                refine ⟨9170811349164794826129629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6113874232776529884086419 9170811349164794826129629)
                ·
                  refine ⟨3439054255936798059798611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9170811349164794826129629 3439054255936798059798611)
                  ·
                    refine ⟨5158581383905197089697917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3439054255936798059798611 5158581383905197089697917)
                    ·
                      refine ⟨1934468018964448908636719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5158581383905197089697917 1934468018964448908636719)
                      ·
                        rfl

theorem cell23_3767363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 1, 3].length) (baseStart_3767363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767363 prefixEnd_3767363 := by exact prefixLift 3767363
  have htrace : WordTrace (prefixWord ++ tailWord_3767363) baseStart_3767363 baseEnd_3767363 := by
    simpa [prefixWord, tailWord_3767363, baseEnd_3767363] using wordTrace_append hprefix tailTrace_3767363
  have hstable : (prefixWord ++ tailWord_3767363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767363).length < 2 ^ (prefixWord ++ tailWord_3767363).sum := by decide
  have hdescent : baseEnd_3767363 < baseStart_3767363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767369 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 2, 5, 4]
def baseStart_3767369 : Nat := 118140960795 + 3767369 * 2 ^ 59
def prefixEnd_3767369 : Nat := 4983230072969 + 3 ^ 40 * 3767369 * 2
def baseEnd_3767369 : Nat := 1934471099848375885161691

theorem tailTrace_3767369 : CollatzResearch.WordTrace tailWord_3767369 prefixEnd_3767369 1934471099848375885161691 := by
  unfold tailWord_3767369
  simp only [CollatzResearch.WordTrace]
  refine ⟨137407235888473003245393161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91604823925648668830262107 137407235888473003245393161)
  ·
    refine ⟨103055426916354752434044871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137407235888473003245393161 103055426916354752434044871)
    ·
      refine ⟨154583140374532128651067307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103055426916354752434044871 154583140374532128651067307)
      ·
        refine ⟨231874710561798192976600961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154583140374532128651067307 231874710561798192976600961)
        ·
          refine ⟨173906032921348644732450721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231874710561798192976600961 173906032921348644732450721)
          ·
            refine ⟨130429524691011483549338041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173906032921348644732450721 130429524691011483549338041)
            ·
              refine ⟨97822143518258612662003531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130429524691011483549338041 97822143518258612662003531)
              ·
                refine ⟨146733215277387918993005297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97822143518258612662003531 146733215277387918993005297)
                ·
                  refine ⟨110049911458040939244753973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146733215277387918993005297 110049911458040939244753973)
                  ·
                    refine ⟨10317179199191338054195685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110049911458040939244753973 10317179199191338054195685)
                    ·
                      refine ⟨1934471099848375885161691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10317179199191338054195685 1934471099848375885161691)
                      ·
                        rfl

theorem cell23_3767369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_3767369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767369 prefixEnd_3767369 := by exact prefixLift 3767369
  have htrace : WordTrace (prefixWord ++ tailWord_3767369) baseStart_3767369 baseEnd_3767369 := by
    simpa [prefixWord, tailWord_3767369, baseEnd_3767369] using wordTrace_append hprefix tailTrace_3767369
  have hstable : (prefixWord ++ tailWord_3767369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767369).length < 2 ^ (prefixWord ++ tailWord_3767369).sum := by decide
  have hdescent : baseEnd_3767369 < baseStart_3767369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767414 : List Nat := [5, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3]
def baseStart_3767414 : Nat := 118140960795 + 3767414 * 2 ^ 59
def prefixEnd_3767414 : Nat := 4983230072969 + 3 ^ 40 * 3767414 * 2
def baseEnd_3767414 : Nat := 1934494206477828209098985

theorem tailTrace_3767414 : CollatzResearch.WordTrace tailWord_3767414 prefixEnd_3767414 1934494206477828209098985 := by
  unfold tailWord_3767414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8588054823331873495673831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91605918115539983953854197 8588054823331873495673831)
  ·
    refine ⟨12882082234997810243510747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8588054823331873495673831 12882082234997810243510747)
    ·
      refine ⟨19323123352496715365266121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12882082234997810243510747 19323123352496715365266121)
      ·
        refine ⟨14492342514372536523949591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19323123352496715365266121 14492342514372536523949591)
        ·
          refine ⟨21738513771558804785924387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14492342514372536523949591 21738513771558804785924387)
          ·
            refine ⟨32607770657338207178886581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21738513771558804785924387 32607770657338207178886581)
            ·
              refine ⟨3056978499125456923020617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32607770657338207178886581 3056978499125456923020617)
              ·
                refine ⟨2292733874344092692265463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3056978499125456923020617 2292733874344092692265463)
                ·
                  refine ⟨3439100811516139038398195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2292733874344092692265463 3439100811516139038398195)
                  ·
                    refine ⟨5158651217274208557597293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3439100811516139038398195 5158651217274208557597293)
                    ·
                      refine ⟨1934494206477828209098985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5158651217274208557597293 1934494206477828209098985)
                      ·
                        rfl

theorem cell23_3767414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_3767414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767414 prefixEnd_3767414 := by exact prefixLift 3767414
  have htrace : WordTrace (prefixWord ++ tailWord_3767414) baseStart_3767414 baseEnd_3767414 := by
    simpa [prefixWord, tailWord_3767414, baseEnd_3767414] using wordTrace_append hprefix tailTrace_3767414
  have hstable : (prefixWord ++ tailWord_3767414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767414).length < 2 ^ (prefixWord ++ tailWord_3767414).sum := by decide
  have hdescent : baseEnd_3767414 < baseStart_3767414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767436 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 5, 3, 3]
def baseStart_3767436 : Nat := 118140960795 + 3767436 * 2 ^ 59
def prefixEnd_3767436 : Nat := 4983230072969 + 3 ^ 40 * 3767436 * 2
def baseEnd_3767436 : Nat := 1934505503052227123023883

theorem tailTrace_3767436 : CollatzResearch.WordTrace tailWord_3767436 prefixEnd_3767436 1934505503052227123023883 := by
  unfold tailWord_3767436
  simp only [CollatzResearch.WordTrace]
  refine ⟨68704839789615136844041081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91606453052820182458721441 68704839789615136844041081)
  ·
    refine ⟨51528629842211352633030811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68704839789615136844041081 51528629842211352633030811)
    ·
      refine ⟨77292944763317028949546217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51528629842211352633030811 77292944763317028949546217)
      ·
        refine ⟨57969708572487771712159663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77292944763317028949546217 57969708572487771712159663)
        ·
          refine ⟨86954562858731657568239495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57969708572487771712159663 86954562858731657568239495)
          ·
            refine ⟨130431844288097486352359243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86954562858731657568239495 130431844288097486352359243)
            ·
              refine ⟨195647766432146229528538865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130431844288097486352359243 195647766432146229528538865)
              ·
                refine ⟨146735824824109672146404149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195647766432146229528538865 146735824824109672146404149)
                ·
                  refine ⟨13756483577260281763725389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146735824824109672146404149 13756483577260281763725389)
                  ·
                    refine ⟨5158681341472605661397021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13756483577260281763725389 5158681341472605661397021)
                    ·
                      refine ⟨1934505503052227123023883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5158681341472605661397021 1934505503052227123023883)
                      ·
                        rfl

theorem cell23_3767436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_3767436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767436 prefixEnd_3767436 := by exact prefixLift 3767436
  have htrace : WordTrace (prefixWord ++ tailWord_3767436) baseStart_3767436 baseEnd_3767436 := by
    simpa [prefixWord, tailWord_3767436, baseEnd_3767436] using wordTrace_append hprefix tailTrace_3767436
  have hstable : (prefixWord ++ tailWord_3767436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767436).length < 2 ^ (prefixWord ++ tailWord_3767436).sum := by decide
  have hdescent : baseEnd_3767436 < baseStart_3767436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767453 : List Nat := [1, 4, 2, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_3767453 : Nat := 118140960795 + 3767453 * 2 ^ 59
def prefixEnd_3767453 : Nat := 4983230072969 + 3 ^ 40 * 3767453 * 2
def baseEnd_3767453 : Nat := 1934514232223353556511305

theorem tailTrace_3767453 : CollatzResearch.WordTrace tailWord_3767453 prefixEnd_3767453 1934514232223353556511305 := by
  unfold tailWord_3767453
  simp only [CollatzResearch.WordTrace]
  refine ⟨137410299620168685591451013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91606866413445790394300675 137410299620168685591451013)
  ·
    refine ⟨25764431178781628548397065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137410299620168685591451013 25764431178781628548397065)
    ·
      refine ⟨19323323384086221411297799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25764431178781628548397065 19323323384086221411297799)
      ·
        refine ⟨28984985076129332116946699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19323323384086221411297799 28984985076129332116946699)
        ·
          refine ⟨43477477614193998175420049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28984985076129332116946699 43477477614193998175420049)
          ·
            refine ⟨32608108210645498631565037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43477477614193998175420049 32608108210645498631565037)
            ·
              refine ⟨12228040578992061986836889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32608108210645498631565037 12228040578992061986836889)
              ·
                refine ⟨9171030434244046490127667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12228040578992061986836889 9171030434244046490127667)
                ·
                  refine ⟨13756545651366069735191501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9171030434244046490127667 13756545651366069735191501)
                  ·
                    refine ⟨5158704619262276150696813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13756545651366069735191501 5158704619262276150696813)
                    ·
                      refine ⟨1934514232223353556511305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5158704619262276150696813 1934514232223353556511305)
                      ·
                        rfl

theorem cell23_3767453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_3767453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767453 prefixEnd_3767453 := by exact prefixLift 3767453
  have htrace : WordTrace (prefixWord ++ tailWord_3767453) baseStart_3767453 baseEnd_3767453 := by
    simpa [prefixWord, tailWord_3767453, baseEnd_3767453] using wordTrace_append hprefix tailTrace_3767453
  have hstable : (prefixWord ++ tailWord_3767453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767453).length < 2 ^ (prefixWord ++ tailWord_3767453).sum := by decide
  have hdescent : baseEnd_3767453 < baseStart_3767453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767494 : List Nat := [6, 1, 2, 2, 1, 1, 3, 7]
def baseStart_3767494 : Nat := 118140960795 + 3767494 * 2 ^ 59
def prefixEnd_3767494 : Nat := 4983230072969 + 3 ^ 40 * 3767494 * 2
def baseEnd_3767494 : Nat := 71649454997414366522171

theorem tailTrace_3767494 : CollatzResearch.WordTrace tailWord_3767494 prefixEnd_3767494 71649454997414366522171 := by
  unfold tailWord_3767494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4294118594156879674802923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91607863342013433062462357 4294118594156879674802923)
  ·
    refine ⟨6441177891235319512204385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4294118594156879674802923 6441177891235319512204385)
    ·
      refine ⟨4830883418426489634153289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6441177891235319512204385 4830883418426489634153289)
      ·
        refine ⟨3623162563819867225614967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4830883418426489634153289 3623162563819867225614967)
        ·
          refine ⟨5434743845729800838422451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3623162563819867225614967 5434743845729800838422451)
          ·
            refine ⟨8152115768594701257633677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5434743845729800838422451 8152115768594701257633677)
            ·
              refine ⟨3057043413223012971612629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8152115768594701257633677 3057043413223012971612629)
              ·
                refine ⟨71649454997414366522171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3057043413223012971612629 71649454997414366522171)
                ·
                  rfl

theorem cell23_3767494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_3767494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767494 prefixEnd_3767494 := by exact prefixLift 3767494
  have htrace : WordTrace (prefixWord ++ tailWord_3767494) baseStart_3767494 baseEnd_3767494 := by
    simpa [prefixWord, tailWord_3767494, baseEnd_3767494] using wordTrace_append hprefix tailTrace_3767494
  have hstable : (prefixWord ++ tailWord_3767494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767494).length < 2 ^ (prefixWord ++ tailWord_3767494).sum := by decide
  have hdescent : baseEnd_3767494 < baseStart_3767494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767496 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_3767496 : Nat := 118140960795 + 3767496 * 2 ^ 59
def prefixEnd_3767496 : Nat := 4983230072969 + 3 ^ 40 * 3767496 * 2
def baseEnd_3767496 : Nat := 1934536311891496888273607

theorem tailTrace_3767496 : CollatzResearch.WordTrace tailWord_3767496 prefixEnd_3767496 1934536311891496888273607 := by
  unfold tailWord_3767496
  simp only [CollatzResearch.WordTrace]
  refine ⟨68705933979506451967633171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91607911972675269290177561 68705933979506451967633171)
  ·
    refine ⟨103058900969259677951449757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68705933979506451967633171 103058900969259677951449757)
    ·
      refine ⟨38647087863472379231793659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103058900969259677951449757 38647087863472379231793659)
      ·
        refine ⟨57970631795208568847690489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38647087863472379231793659 57970631795208568847690489)
        ·
          refine ⟨43477973846406426635767867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57970631795208568847690489 43477973846406426635767867)
          ·
            refine ⟨65216960769609639953651801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43477973846406426635767867 65216960769609639953651801)
            ·
              refine ⟨48912720577207229965238851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65216960769609639953651801 48912720577207229965238851)
              ·
                refine ⟨73369080865810844947858277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48912720577207229965238851 73369080865810844947858277)
                ·
                  refine ⟨13756702662339533427723427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73369080865810844947858277 13756702662339533427723427)
                  ·
                    refine ⟨20635053993509300141585141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13756702662339533427723427 20635053993509300141585141)
                    ·
                      refine ⟨1934536311891496888273607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20635053993509300141585141 1934536311891496888273607)
                      ·
                        rfl

theorem cell23_3767496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_3767496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767496 prefixEnd_3767496 := by exact prefixLift 3767496
  have htrace : WordTrace (prefixWord ++ tailWord_3767496) baseStart_3767496 baseEnd_3767496 := by
    simpa [prefixWord, tailWord_3767496, baseEnd_3767496] using wordTrace_append hprefix tailTrace_3767496
  have hstable : (prefixWord ++ tailWord_3767496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767496).length < 2 ^ (prefixWord ++ tailWord_3767496).sum := by decide
  have hdescent : baseEnd_3767496 < baseStart_3767496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767533 : List Nat := [1, 5, 1, 2, 2, 1, 1, 3, 7]
def baseStart_3767533 : Nat := 118140960795 + 3767533 * 2 ^ 59
def prefixEnd_3767533 : Nat := 4983230072969 + 3 ^ 40 * 3767533 * 2
def baseEnd_3767533 : Nat := 214950590075079249278993

theorem tailTrace_3767533 : CollatzResearch.WordTrace tailWord_3767533 prefixEnd_3767533 214950590075079249278993 := by
  unfold tailWord_3767533
  simp only [CollatzResearch.WordTrace]
  refine ⟨137413217459878859254363253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91608811639919239502908835 137413217459878859254363253)
  ·
    refine ⟨12882489136863643055096555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137413217459878859254363253 12882489136863643055096555)
    ·
      refine ⟨19323733705295464582644833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12882489136863643055096555 19323733705295464582644833)
      ·
        refine ⟨14492800278971598436983625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19323733705295464582644833 14492800278971598436983625)
        ·
          refine ⟨10869600209228698827737719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14492800278971598436983625 10869600209228698827737719)
          ·
            refine ⟨16304400313843048241606579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10869600209228698827737719 16304400313843048241606579)
            ·
              refine ⟨24456600470764572362409869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16304400313843048241606579 24456600470764572362409869)
              ·
                refine ⟨9171225176536714635903701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24456600470764572362409869 9171225176536714635903701)
                ·
                  refine ⟨214950590075079249278993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9171225176536714635903701 214950590075079249278993)
                  ·
                    rfl

theorem cell23_3767533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_3767533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767533 prefixEnd_3767533 := by exact prefixLift 3767533
  have htrace : WordTrace (prefixWord ++ tailWord_3767533) baseStart_3767533 baseEnd_3767533 := by
    simpa [prefixWord, tailWord_3767533, baseEnd_3767533] using wordTrace_append hprefix tailTrace_3767533
  have hstable : (prefixWord ++ tailWord_3767533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767533).length < 2 ^ (prefixWord ++ tailWord_3767533).sum := by decide
  have hdescent : baseEnd_3767533 < baseStart_3767533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767546 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 3, 7]
def baseStart_3767546 : Nat := 118140960795 + 3767546 * 2 ^ 59
def prefixEnd_3767546 : Nat := 4983230072969 + 3 ^ 40 * 3767546 * 2
def baseEnd_3767546 : Nat := 644853995308073897549459

theorem tailTrace_3767546 : CollatzResearch.WordTrace tailWord_3767546 prefixEnd_3767546 644853995308073897549459 := by
  unfold tailWord_3767546
  simp only [CollatzResearch.WordTrace]
  refine ⟨34353422902207940618646623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91609127739221174983057661 34353422902207940618646623)
  ·
    refine ⟨51530134353311910927969935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34353422902207940618646623 51530134353311910927969935)
    ·
      refine ⟨77295201529967866391954903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51530134353311910927969935 77295201529967866391954903)
      ·
        refine ⟨115942802294951799587932355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77295201529967866391954903 115942802294951799587932355)
        ·
          refine ⟨173914203442427699381898533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115942802294951799587932355 173914203442427699381898533)
          ·
            refine ⟨32608913145455193634105975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173914203442427699381898533 32608913145455193634105975)
            ·
              refine ⟨48913369718182790451158963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32608913145455193634105975 48913369718182790451158963)
              ·
                refine ⟨73370054577274185676738445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48913369718182790451158963 73370054577274185676738445)
                ·
                  refine ⟨27513770466477819628776917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73370054577274185676738445 27513770466477819628776917)
                  ·
                    refine ⟨644853995308073897549459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27513770466477819628776917 644853995308073897549459)
                    ·
                      rfl

theorem cell23_3767546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_3767546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767546 prefixEnd_3767546 := by exact prefixLift 3767546
  have htrace : WordTrace (prefixWord ++ tailWord_3767546) baseStart_3767546 baseEnd_3767546 := by
    simpa [prefixWord, tailWord_3767546, baseEnd_3767546] using wordTrace_append hprefix tailTrace_3767546
  have hstable : (prefixWord ++ tailWord_3767546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767546).length < 2 ^ (prefixWord ++ tailWord_3767546).sum := by decide
  have hdescent : baseEnd_3767546 < baseStart_3767546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767617 : List Nat := [1, 2, 5, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3767617 : Nat := 118140960795 + 3767617 * 2 ^ 59
def prefixEnd_3767617 : Nat := 4983230072969 + 3 ^ 40 * 3767617 * 2
def baseEnd_3767617 : Nat := 1934598443050690914860551

theorem tailTrace_3767617 : CollatzResearch.WordTrace tailWord_3767617 prefixEnd_3767617 1934598443050690914860551 := by
  unfold tailWord_3767617
  simp only [CollatzResearch.WordTrace]
  refine ⟨137416281191574541600421105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91610854127716361066947403 137416281191574541600421105)
  ·
    refine ⟨103062210893680906200315829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137416281191574541600421105 103062210893680906200315829)
    ·
      refine ⟨9662082271282584956279609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103062210893680906200315829 9662082271282584956279609)
      ·
        refine ⟨7246561703461938717209707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9662082271282584956279609 7246561703461938717209707)
        ·
          refine ⟨10869842555192908075814561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7246561703461938717209707 10869842555192908075814561)
          ·
            refine ⟨8152381916394681056860921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10869842555192908075814561 8152381916394681056860921)
            ·
              refine ⟨6114286437296010792645691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8152381916394681056860921 6114286437296010792645691)
              ·
                refine ⟨9171429655944016188968537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6114286437296010792645691 9171429655944016188968537)
                ·
                  refine ⟨6878572241958012141726403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9171429655944016188968537 6878572241958012141726403)
                  ·
                    refine ⟨10317858362937018212589605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6878572241958012141726403 10317858362937018212589605)
                    ·
                      refine ⟨1934598443050690914860551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10317858362937018212589605 1934598443050690914860551)
                      ·
                        rfl

theorem cell23_3767617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3767617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767617 prefixEnd_3767617 := by exact prefixLift 3767617
  have htrace : WordTrace (prefixWord ++ tailWord_3767617) baseStart_3767617 baseEnd_3767617 := by
    simpa [prefixWord, tailWord_3767617, baseEnd_3767617] using wordTrace_append hprefix tailTrace_3767617
  have hstable : (prefixWord ++ tailWord_3767617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767617).length < 2 ^ (prefixWord ++ tailWord_3767617).sum := by decide
  have hdescent : baseEnd_3767617 < baseStart_3767617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767653 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 5, 5]
def baseStart_3767653 : Nat := 118140960795 + 3767653 * 2 ^ 59
def prefixEnd_3767653 : Nat := 4983230072969 + 3 ^ 40 * 3767653 * 2
def baseEnd_3767653 : Nat := 644872309451417591336795

theorem tailTrace_3767653 : CollatzResearch.WordTrace tailWord_3767653 prefixEnd_3767653 644872309451417591336795 := by
  unfold tailWord_3767653
  simp only [CollatzResearch.WordTrace]
  refine ⟨137417594219444119748731613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91611729479629413165821075 137417594219444119748731613)
  ·
    refine ⟨51531597832291544905774355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137417594219444119748731613 51531597832291544905774355)
    ·
      refine ⟨77297396748437317358661533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51531597832291544905774355 77297396748437317358661533)
      ·
        refine ⟨28986523780663994009498075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77297396748437317358661533 28986523780663994009498075)
        ·
          refine ⟨43479785670995991014247113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28986523780663994009498075 43479785670995991014247113)
          ·
            refine ⟨32609839253246993260685335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43479785670995991014247113 32609839253246993260685335)
            ·
              refine ⟨48914758879870489891028003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32609839253246993260685335 48914758879870489891028003)
              ·
                refine ⟨73372138319805734836542005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48914758879870489891028003 73372138319805734836542005)
                ·
                  refine ⟨6878637967481787640925813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73372138319805734836542005 6878637967481787640925813)
                  ·
                    refine ⟨644872309451417591336795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6878637967481787640925813 644872309451417591336795)
                    ·
                      rfl

theorem cell23_3767653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_3767653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767653 prefixEnd_3767653 := by exact prefixLift 3767653
  have htrace : WordTrace (prefixWord ++ tailWord_3767653) baseStart_3767653 baseEnd_3767653 := by
    simpa [prefixWord, tailWord_3767653, baseEnd_3767653] using wordTrace_append hprefix tailTrace_3767653
  have hstable : (prefixWord ++ tailWord_3767653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767653).length < 2 ^ (prefixWord ++ tailWord_3767653).sum := by decide
  have hdescent : baseEnd_3767653 < baseStart_3767653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767678 : List Nat := [4, 2, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_3767678 : Nat := 118140960795 + 3767678 * 2 ^ 59
def prefixEnd_3767678 : Nat := 4983230072969 + 3 ^ 40 * 3767678 * 2
def baseEnd_3767678 : Nat := 644876588456871725399257

theorem tailTrace_3767678 : CollatzResearch.WordTrace tailWord_3767678 prefixEnd_3767678 644876588456871725399257 := by
  unfold tailWord_3767678
  simp only [CollatzResearch.WordTrace]
  refine ⟨17177313255544193627298961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91612337362902366012261125 17177313255544193627298961)
  ·
    refine ⟨12882984941658145220474221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17177313255544193627298961 12882984941658145220474221)
    ·
      refine ⟨4831119353121804457677833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12882984941658145220474221 4831119353121804457677833)
      ·
        refine ⟨3623339514841353343258375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4831119353121804457677833 3623339514841353343258375)
        ·
          refine ⟨5435009272262030014887563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3623339514841353343258375 5435009272262030014887563)
          ·
            refine ⟨8152513908393045022331345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5435009272262030014887563 8152513908393045022331345)
            ·
              refine ⟨6114385431294783766748509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8152513908393045022331345 6114385431294783766748509)
              ·
                refine ⟨2292894536735543912530691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6114385431294783766748509 2292894536735543912530691)
                ·
                  refine ⟨3439341805103315868796037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2292894536735543912530691 3439341805103315868796037)
                  ·
                    refine ⟨644876588456871725399257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3439341805103315868796037 644876588456871725399257)
                    ·
                      rfl

theorem cell23_3767678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_3767678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767678 prefixEnd_3767678 := by exact prefixLift 3767678
  have htrace : WordTrace (prefixWord ++ tailWord_3767678) baseStart_3767678 baseEnd_3767678 := by
    simpa [prefixWord, tailWord_3767678, baseEnd_3767678] using wordTrace_append hprefix tailTrace_3767678
  have hstable : (prefixWord ++ tailWord_3767678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767678).length < 2 ^ (prefixWord ++ tailWord_3767678).sum := by decide
  have hdescent : baseEnd_3767678 < baseStart_3767678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767684 : List Nat := [2, 3, 2, 1, 1, 3, 1, 5, 1, 1, 3]
def baseStart_3767684 : Nat := 118140960795 + 3767684 * 2 ^ 59
def prefixEnd_3767684 : Nat := 4983230072969 + 3 ^ 40 * 3767684 * 2
def baseEnd_3767684 : Nat := 1934632846254542152722743

theorem tailTrace_3767684 : CollatzResearch.WordTrace tailWord_3767684 prefixEnd_3767684 1934632846254542152722743 := by
  unfold tailWord_3767684
  simp only [CollatzResearch.WordTrace]
  refine ⟨68709362441165906021555053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91612483254887874695406737 68709362441165906021555053)
  ·
    refine ⟨25766010915437214758083145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68709362441165906021555053 25766010915437214758083145)
    ·
      refine ⟨19324508186577911068562359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25766010915437214758083145 19324508186577911068562359)
      ·
        refine ⟨28986762279866866602843539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19324508186577911068562359 28986762279866866602843539)
        ·
          refine ⟨43480143419800299904265309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28986762279866866602843539 43480143419800299904265309)
          ·
            refine ⟨16305053782425112464099491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43480143419800299904265309 16305053782425112464099491)
            ·
              refine ⟨24457580673637668696149237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16305053782425112464099491 24457580673637668696149237)
              ·
                refine ⟨2292898188153531440263991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24457580673637668696149237 2292898188153531440263991)
                ·
                  refine ⟨3439347282230297160395987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2292898188153531440263991 3439347282230297160395987)
                  ·
                    refine ⟨5159020923345445740593981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3439347282230297160395987 5159020923345445740593981)
                    ·
                      refine ⟨1934632846254542152722743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5159020923345445740593981 1934632846254542152722743)
                      ·
                        rfl

theorem cell23_3767684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_3767684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767684 prefixEnd_3767684 := by exact prefixLift 3767684
  have htrace : WordTrace (prefixWord ++ tailWord_3767684) baseStart_3767684 baseEnd_3767684 := by
    simpa [prefixWord, tailWord_3767684, baseEnd_3767684] using wordTrace_append hprefix tailTrace_3767684
  have hstable : (prefixWord ++ tailWord_3767684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767684).length < 2 ^ (prefixWord ++ tailWord_3767684).sum := by decide
  have hdescent : baseEnd_3767684 < baseStart_3767684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767687 : List Nat := [1, 1, 4, 2, 2, 2, 4, 1, 1, 5]
def baseStart_3767687 : Nat := 118140960795 + 3767687 * 2 ^ 59
def prefixEnd_3767687 : Nat := 4983230072969 + 3 ^ 40 * 3767687 * 2
def baseEnd_3767687 : Nat := 644878128898835213661743

theorem tailTrace_3767687 : CollatzResearch.WordTrace tailWord_3767687 prefixEnd_3767687 644878128898835213661743 := by
  unfold tailWord_3767687
  simp only [CollatzResearch.WordTrace]
  refine ⟨137418834301320943555469315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91612556200880629036979543 137418834301320943555469315)
  ·
    refine ⟨206128251451981415333203973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137418834301320943555469315 206128251451981415333203973)
    ·
      refine ⟨38649047147246515374975745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206128251451981415333203973 38649047147246515374975745)
      ·
        refine ⟨28986785360434886531231809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38649047147246515374975745 28986785360434886531231809)
        ·
          refine ⟨21740089020326164898423857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28986785360434886531231809 21740089020326164898423857)
          ·
            refine ⟨16305066765244623673817893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21740089020326164898423857 16305066765244623673817893)
            ·
              refine ⟨3057200018483366938840855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16305066765244623673817893 3057200018483366938840855)
              ·
                refine ⟨4585800027725050408261283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3057200018483366938840855 4585800027725050408261283)
                ·
                  refine ⟨6878700041587575612391925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4585800027725050408261283 6878700041587575612391925)
                  ·
                    refine ⟨644878128898835213661743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6878700041587575612391925 644878128898835213661743)
                    ·
                      rfl

theorem cell23_3767687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_3767687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767687 prefixEnd_3767687 := by exact prefixLift 3767687
  have htrace : WordTrace (prefixWord ++ tailWord_3767687) baseStart_3767687 baseEnd_3767687 := by
    simpa [prefixWord, tailWord_3767687, baseEnd_3767687] using wordTrace_append hprefix tailTrace_3767687
  have hstable : (prefixWord ++ tailWord_3767687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767687).length < 2 ^ (prefixWord ++ tailWord_3767687).sum := by decide
  have hdescent : baseEnd_3767687 < baseStart_3767687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767703 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 6]
def baseStart_3767703 : Nat := 118140960795 + 3767703 * 2 ^ 59
def prefixEnd_3767703 : Nat := 4983230072969 + 3 ^ 40 * 3767703 * 2
def baseEnd_3767703 : Nat := 1934642602386977578385155

theorem tailTrace_3767703 : CollatzResearch.WordTrace tailWord_3767703 prefixEnd_3767703 1934642602386977578385155 := by
  unfold tailWord_3767703
  simp only [CollatzResearch.WordTrace]
  refine ⟨137419417869262978288051763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91612945246175318858701175 137419417869262978288051763)
  ·
    refine ⟨206129126803894467432077645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137419417869262978288051763 206129126803894467432077645)
    ·
      refine ⟨77298422551460425287029117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206129126803894467432077645 77298422551460425287029117)
      ·
        refine ⟨28986908456797659482635919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77298422551460425287029117 28986908456797659482635919)
        ·
          refine ⟨43480362685196489223953879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28986908456797659482635919 43480362685196489223953879)
          ·
            refine ⟨65220544027794733835930819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43480362685196489223953879 65220544027794733835930819)
            ·
              refine ⟨97830816041692100753896229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65220544027794733835930819 97830816041692100753896229)
              ·
                refine ⟨18343278007817268891355543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97830816041692100753896229 18343278007817268891355543)
                ·
                  refine ⟨27514917011725903337033315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18343278007817268891355543 27514917011725903337033315)
                  ·
                    refine ⟨41272375517588855005549973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27514917011725903337033315 41272375517588855005549973)
                    ·
                      refine ⟨1934642602386977578385155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41272375517588855005549973 1934642602386977578385155)
                      ·
                        rfl

theorem cell23_3767703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_3767703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767703 prefixEnd_3767703 := by exact prefixLift 3767703
  have htrace : WordTrace (prefixWord ++ tailWord_3767703) baseStart_3767703 baseEnd_3767703 := by
    simpa [prefixWord, tailWord_3767703, baseEnd_3767703] using wordTrace_append hprefix tailTrace_3767703
  have hstable : (prefixWord ++ tailWord_3767703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767703).length < 2 ^ (prefixWord ++ tailWord_3767703).sum := by decide
  have hdescent : baseEnd_3767703 < baseStart_3767703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767753 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 4, 2, 5]
def baseStart_3767753 : Nat := 118140960795 + 3767753 * 2 ^ 59
def prefixEnd_3767753 : Nat := 4983230072969 + 3 ^ 40 * 3767753 * 2
def baseEnd_3767753 : Nat := 1934668276419702382759925

theorem tailTrace_3767753 : CollatzResearch.WordTrace tailWord_3767753 prefixEnd_3767753 1934668276419702382759925 := by
  unfold tailWord_3767753
  simp only [CollatzResearch.WordTrace]
  refine ⟨137421241519081836827371913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91614161012721224551581275 137421241519081836827371913)
  ·
    refine ⟨103065931139311377620528935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137421241519081836827371913 103065931139311377620528935)
    ·
      refine ⟨154598896708967066430793403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103065931139311377620528935 154598896708967066430793403)
      ·
        refine ⟨231898345063450599646190105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154598896708967066430793403 231898345063450599646190105)
        ·
          refine ⟨173923758797587949734642579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231898345063450599646190105 173923758797587949734642579)
          ·
            refine ⟨260885638196381924601963869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173923758797587949734642579 260885638196381924601963869)
            ·
              refine ⟨97832114323643221725736451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260885638196381924601963869 97832114323643221725736451)
              ·
                refine ⟨146748171485464832588604677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97832114323643221725736451 146748171485464832588604677)
                ·
                  refine ⟨27515282153524656110363377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146748171485464832588604677 27515282153524656110363377)
                  ·
                    refine ⟨20636461615143492082772533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27515282153524656110363377 20636461615143492082772533)
                    ·
                      refine ⟨1934668276419702382759925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20636461615143492082772533 1934668276419702382759925)
                      ·
                        rfl

theorem cell23_3767753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_3767753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767753 prefixEnd_3767753 := by exact prefixLift 3767753
  have htrace : WordTrace (prefixWord ++ tailWord_3767753) baseStart_3767753 baseEnd_3767753 := by
    simpa [prefixWord, tailWord_3767753, baseEnd_3767753] using wordTrace_append hprefix tailTrace_3767753
  have hstable : (prefixWord ++ tailWord_3767753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767753).length < 2 ^ (prefixWord ++ tailWord_3767753).sum := by decide
  have hdescent : baseEnd_3767753 < baseStart_3767753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767800 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 2, 1, 5]
def baseStart_3767800 : Nat := 118140960795 + 3767800 * 2 ^ 59
def prefixEnd_3767800 : Nat := 4983230072969 + 3 ^ 40 * 3767800 * 2
def baseEnd_3767800 : Nat := 1934692410010463698872209

theorem tailTrace_3767800 : CollatzResearch.WordTrace tailWord_3767800 prefixEnd_3767800 1934692410010463698872209 := by
  unfold tailWord_3767800
  simp only [CollatzResearch.WordTrace]
  refine ⟨68711477874955781927166427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91615303833274375902888569 68711477874955781927166427)
  ·
    refine ⟨103067216812433672890749641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68711477874955781927166427 103067216812433672890749641)
    ·
      refine ⟨77300412609325254668062231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103067216812433672890749641 77300412609325254668062231)
      ·
        refine ⟨115950618913987882002093347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77300412609325254668062231 115950618913987882002093347)
        ·
          refine ⟨173925928370981823003140021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115950618913987882002093347 173925928370981823003140021)
          ·
            refine ⟨16305555784779545906544377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173925928370981823003140021 16305555784779545906544377)
            ·
              refine ⟨12229166838584659429908283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16305555784779545906544377 12229166838584659429908283)
              ·
                refine ⟨18343750257876989144862425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12229166838584659429908283 18343750257876989144862425)
                ·
                  refine ⟨13757812693407741858646819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18343750257876989144862425 13757812693407741858646819)
                  ·
                    refine ⟨20636719040111612787970229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13757812693407741858646819 20636719040111612787970229)
                    ·
                      refine ⟨1934692410010463698872209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20636719040111612787970229 1934692410010463698872209)
                      ·
                        rfl

theorem cell23_3767800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_3767800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767800 prefixEnd_3767800 := by exact prefixLift 3767800
  have htrace : WordTrace (prefixWord ++ tailWord_3767800) baseStart_3767800 baseEnd_3767800 := by
    simpa [prefixWord, tailWord_3767800, baseEnd_3767800] using wordTrace_append hprefix tailTrace_3767800
  have hstable : (prefixWord ++ tailWord_3767800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767800).length < 2 ^ (prefixWord ++ tailWord_3767800).sum := by decide
  have hdescent : baseEnd_3767800 < baseStart_3767800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767803 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 9]
def baseStart_3767803 : Nat := 118140960795 + 3767803 * 2 ^ 59
def prefixEnd_3767803 : Nat := 4983230072969 + 3 ^ 40 * 3767803 * 2
def baseEnd_3767803 : Nat := 214965994494714131903855

theorem tailTrace_3767803 : CollatzResearch.WordTrace tailWord_3767803 prefixEnd_3767803 214965994494714131903855 := by
  unfold tailWord_3767803
  simp only [CollatzResearch.WordTrace]
  refine ⟨137423065168900695366692063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91615376779267130244461375 137423065168900695366692063)
  ·
    refine ⟨206134597753351043050038095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137423065168900695366692063 206134597753351043050038095)
    ·
      refine ⟨309201896630026564575057143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206134597753351043050038095 309201896630026564575057143)
      ·
        refine ⟨463802844945039846862585715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309201896630026564575057143 463802844945039846862585715)
        ·
          refine ⟨695704267417559770293878573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463802844945039846862585715 695704267417559770293878573)
          ·
            refine ⟨260889100281584913860204465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 695704267417559770293878573 260889100281584913860204465)
            ·
              refine ⟨195666825211188685395153349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260889100281584913860204465 195666825211188685395153349)
              ·
                refine ⟨36687529727097878511591253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195666825211188685395153349 36687529727097878511591253)
                ·
                  refine ⟨214965994494714131903855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36687529727097878511591253 214965994494714131903855)
                  ·
                    rfl

theorem cell23_3767803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 9].length) (baseStart_3767803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767803 prefixEnd_3767803 := by exact prefixLift 3767803
  have htrace : WordTrace (prefixWord ++ tailWord_3767803) baseStart_3767803 baseEnd_3767803 := by
    simpa [prefixWord, tailWord_3767803, baseEnd_3767803] using wordTrace_append hprefix tailTrace_3767803
  have hstable : (prefixWord ++ tailWord_3767803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767803).length < 2 ^ (prefixWord ++ tailWord_3767803).sum := by decide
  have hdescent : baseEnd_3767803 < baseStart_3767803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767854 : List Nat := [4, 1, 3, 1, 2, 1, 1, 5, 5]
def baseStart_3767854 : Nat := 118140960795 + 3767854 * 2 ^ 59
def prefixEnd_3767854 : Nat := 4983230072969 + 3 ^ 40 * 3767854 * 2
def baseEnd_3767854 : Nat := 214968904218422943066329

theorem tailTrace_3767854 : CollatzResearch.WordTrace tailWord_3767854 prefixEnd_3767854 214968904218422943066329 := by
  unfold tailWord_3767854
  simp only [CollatzResearch.WordTrace]
  refine ⟨17178115661464491384599827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91616616861143954051199077 17178115661464491384599827)
  ·
    refine ⟨25767173492196737076899741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17178115661464491384599827 25767173492196737076899741)
    ·
      refine ⟨9662690059573776403837403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25767173492196737076899741 9662690059573776403837403)
      ·
        refine ⟨14494035089360664605756105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9662690059573776403837403 14494035089360664605756105)
        ·
          refine ⟨10870526317020498454317079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14494035089360664605756105 10870526317020498454317079)
          ·
            refine ⟨16305789475530747681475619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10870526317020498454317079 16305789475530747681475619)
            ·
              refine ⟨24458684213296121522213429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16305789475530747681475619 24458684213296121522213429)
              ·
                refine ⟨2293001644996511392707509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24458684213296121522213429 2293001644996511392707509)
                ·
                  refine ⟨214968904218422943066329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2293001644996511392707509 214968904218422943066329)
                  ·
                    rfl

theorem cell23_3767854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_3767854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767854 prefixEnd_3767854 := by exact prefixLift 3767854
  have htrace : WordTrace (prefixWord ++ tailWord_3767854) baseStart_3767854 baseEnd_3767854 := by
    simpa [prefixWord, tailWord_3767854, baseEnd_3767854] using wordTrace_append hprefix tailTrace_3767854
  have hstable : (prefixWord ++ tailWord_3767854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767854).length < 2 ^ (prefixWord ++ tailWord_3767854).sum := by decide
  have hdescent : baseEnd_3767854 < baseStart_3767854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767907 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 3]
def baseStart_3767907 : Nat := 118140960795 + 3767907 * 2 ^ 59
def prefixEnd_3767907 : Nat := 4983230072969 + 3 ^ 40 * 3767907 * 2
def baseEnd_3767907 : Nat := 1934747352440494780234217

theorem tailTrace_3767907 : CollatzResearch.WordTrace tailWord_3767907 prefixEnd_3767907 1934747352440494780234217 := by
  unfold tailWord_3767907
  simp only [CollatzResearch.WordTrace]
  refine ⟨137426858360523921128477975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91617905573682614085651983 137426858360523921128477975)
  ·
    refine ⟨206140287540785881692716963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137426858360523921128477975 206140287540785881692716963)
    ·
      refine ⟨309210431311178822539075445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206140287540785881692716963 309210431311178822539075445)
      ·
        refine ⟨28988477935423014613038323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 309210431311178822539075445 28988477935423014613038323)
        ·
          refine ⟨43482716903134521919557485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28988477935423014613038323 43482716903134521919557485)
          ·
            refine ⟨16306018838675445719834057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43482716903134521919557485 16306018838675445719834057)
            ·
              refine ⟨12229514129006584289875543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16306018838675445719834057 12229514129006584289875543)
              ·
                refine ⟨18344271193509876434813315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12229514129006584289875543 18344271193509876434813315)
                ·
                  refine ⟨27516406790264814652219973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18344271193509876434813315 27516406790264814652219973)
                  ·
                    refine ⟨5159326273174652747291245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27516406790264814652219973 5159326273174652747291245)
                    ·
                      refine ⟨1934747352440494780234217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5159326273174652747291245 1934747352440494780234217)
                      ·
                        rfl

theorem cell23_3767907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_3767907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767907 prefixEnd_3767907 := by exact prefixLift 3767907
  have htrace : WordTrace (prefixWord ++ tailWord_3767907) baseStart_3767907 baseEnd_3767907 := by
    simpa [prefixWord, tailWord_3767907, baseEnd_3767907] using wordTrace_append hprefix tailTrace_3767907
  have hstable : (prefixWord ++ tailWord_3767907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767907).length < 2 ^ (prefixWord ++ tailWord_3767907).sum := by decide
  have hdescent : baseEnd_3767907 < baseStart_3767907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767930 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6]
def baseStart_3767930 : Nat := 118140960795 + 3767930 * 2 ^ 59
def prefixEnd_3767930 : Nat := 4983230072969 + 3 ^ 40 * 3767930 * 2
def baseEnd_3767930 : Nat := 1934759162495548190246611

theorem tailTrace_3767930 : CollatzResearch.WordTrace tailWord_3767930 prefixEnd_3767930 1934759162495548190246611 := by
  unfold tailWord_3767930
  simp only [CollatzResearch.WordTrace]
  refine ⟨34356924309860149014141311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91618464826293730704376829 34356924309860149014141311)
  ·
    refine ⟨51535386464790223521211967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34356924309860149014141311 51535386464790223521211967)
    ·
      refine ⟨77303079697185335281817951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51535386464790223521211967 77303079697185335281817951)
      ·
        refine ⟨115954619545778002922726927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77303079697185335281817951 115954619545778002922726927)
        ·
          refine ⟨173931929318667004384090391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115954619545778002922726927 173931929318667004384090391)
          ·
            refine ⟨260897893978000506576135587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173931929318667004384090391 260897893978000506576135587)
            ·
              refine ⟨391346840967000759864203381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260897893978000506576135587 391346840967000759864203381)
              ·
                refine ⟨36688766340656321237269067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 391346840967000759864203381 36688766340656321237269067)
                ·
                  refine ⟨55033149510984481855903601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36688766340656321237269067 55033149510984481855903601)
                  ·
                    refine ⟨41274862133238361391927701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55033149510984481855903601 41274862133238361391927701)
                    ·
                      refine ⟨1934759162495548190246611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41274862133238361391927701 1934759162495548190246611)
                      ·
                        rfl

theorem cell23_3767930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_3767930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767930 prefixEnd_3767930 := by exact prefixLift 3767930
  have htrace : WordTrace (prefixWord ++ tailWord_3767930) baseStart_3767930 baseEnd_3767930 := by
    simpa [prefixWord, tailWord_3767930, baseEnd_3767930] using wordTrace_append hprefix tailTrace_3767930
  have hstable : (prefixWord ++ tailWord_3767930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767930).length < 2 ^ (prefixWord ++ tailWord_3767930).sum := by decide
  have hdescent : baseEnd_3767930 < baseStart_3767930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767931 : List Nat := [1, 1, 1, 1, 1, 4, 7, 2, 1, 4]
def baseStart_3767931 : Nat := 118140960795 + 3767931 * 2 ^ 59
def prefixEnd_3767931 : Nat := 4983230072969 + 3 ^ 40 * 3767931 * 2
def baseEnd_3767931 : Nat := 644919891992067562111369

theorem tailTrace_3767931 : CollatzResearch.WordTrace tailWord_3767931 prefixEnd_3767931 644919891992067562111369 := by
  unfold tailWord_3767931
  simp only [CollatzResearch.WordTrace]
  refine ⟨137427733712436973227351647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91618489141624648818234431 137427733712436973227351647)
  ·
    refine ⟨206141600568655459841027471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137427733712436973227351647 206141600568655459841027471)
    ·
      refine ⟨309212400852983189761541207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206141600568655459841027471 309212400852983189761541207)
      ·
        refine ⟨463818601279474784642311811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309212400852983189761541207 463818601279474784642311811)
        ·
          refine ⟨695727901919212176963467717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463818601279474784642311811 695727901919212176963467717)
          ·
            refine ⟨130448981609852283180650197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 695727901919212176963467717 130448981609852283180650197)
            ·
              refine ⟨3057398006480912887046489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 130448981609852283180650197 3057398006480912887046489)
              ·
                refine ⟨2293048504860684665284867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3057398006480912887046489 2293048504860684665284867)
                ·
                  refine ⟨3439572757291026997927301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293048504860684665284867 3439572757291026997927301)
                  ·
                    refine ⟨644919891992067562111369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3439572757291026997927301 644919891992067562111369)
                    ·
                      rfl

theorem cell23_3767931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 1, 4].length) (baseStart_3767931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767931 prefixEnd_3767931 := by exact prefixLift 3767931
  have htrace : WordTrace (prefixWord ++ tailWord_3767931) baseStart_3767931 baseEnd_3767931 := by
    simpa [prefixWord, tailWord_3767931, baseEnd_3767931] using wordTrace_append hprefix tailTrace_3767931
  have hstable : (prefixWord ++ tailWord_3767931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767931).length < 2 ^ (prefixWord ++ tailWord_3767931).sum := by decide
  have hdescent : baseEnd_3767931 < baseStart_3767931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767971 : List Nat := [1, 1, 1, 4, 1, 1, 4, 5, 1, 1, 3]
def baseStart_3767971 : Nat := 118140960795 + 3767971 * 2 ^ 59
def prefixEnd_3767971 : Nat := 4983230072969 + 3 ^ 40 * 3767971 * 2
def baseEnd_3767971 : Nat := 1934780215202382529833923

theorem tailTrace_3767971 : CollatzResearch.WordTrace tailWord_3767971 prefixEnd_3767971 1934780215202382529833923 := by
  unfold tailWord_3767971
  simp only [CollatzResearch.WordTrace]
  refine ⟨137429192632292060058807767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91619461754861373372538511 137429192632292060058807767)
  ·
    refine ⟨206143788948438090088211651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137429192632292060058807767 206143788948438090088211651)
    ·
      refine ⟨309215683422657135132317477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206143788948438090088211651 309215683422657135132317477)
      ·
        refine ⟨57977940641748212837309527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309215683422657135132317477 57977940641748212837309527)
        ·
          refine ⟨86966910962622319255964291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57977940641748212837309527 86966910962622319255964291)
          ·
            refine ⟨130450366443933478883946437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86966910962622319255964291 130450366443933478883946437)
            ·
              refine ⟨24459443708237527290739957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130450366443933478883946437 24459443708237527290739957)
              ·
                refine ⟨2293072847647268183506871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24459443708237527290739957 2293072847647268183506871)
                ·
                  refine ⟨3439609271470902275260307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293072847647268183506871 3439609271470902275260307)
                  ·
                    refine ⟨5159413907206353412890461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3439609271470902275260307 5159413907206353412890461)
                    ·
                      refine ⟨1934780215202382529833923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5159413907206353412890461 1934780215202382529833923)
                      ·
                        rfl

theorem cell23_3767971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_3767971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767971 prefixEnd_3767971 := by exact prefixLift 3767971
  have htrace : WordTrace (prefixWord ++ tailWord_3767971) baseStart_3767971 baseEnd_3767971 := by
    simpa [prefixWord, tailWord_3767971, baseEnd_3767971] using wordTrace_append hprefix tailTrace_3767971
  have hstable : (prefixWord ++ tailWord_3767971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767971).length < 2 ^ (prefixWord ++ tailWord_3767971).sum := by decide
  have hdescent : baseEnd_3767971 < baseStart_3767971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767981 : List Nat := [1, 5, 2, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_3767981 : Nat := 118140960795 + 3767981 * 2 ^ 59
def prefixEnd_3767981 : Nat := 4983230072969 + 3 ^ 40 * 3767981 * 2
def baseEnd_3767981 : Nat := 1934785350008927490708877

theorem tailTrace_3767981 : CollatzResearch.WordTrace tailWord_3767981 prefixEnd_3767981 1934785350008927490708877 := by
  unfold tailWord_3767981
  simp only [CollatzResearch.WordTrace]
  refine ⟨137429557362255831766671797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91619704908170554511114531 137429557362255831766671797)
  ·
    refine ⟨12884021002711484228125481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137429557362255831766671797 12884021002711484228125481)
    ·
      refine ⟨9663015752033613171094111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12884021002711484228125481 9663015752033613171094111)
      ·
        refine ⟨14494523628050419756641167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9663015752033613171094111 14494523628050419756641167)
        ·
          refine ⟨21741785442075629634961751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14494523628050419756641167 21741785442075629634961751)
          ·
            refine ⟨32612678163113444452442627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21741785442075629634961751 32612678163113444452442627)
            ·
              refine ⟨48919017244670166678663941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32612678163113444452442627 48919017244670166678663941)
              ·
                refine ⟨9172315733375656252249489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48919017244670166678663941 9172315733375656252249489)
                ·
                  refine ⟨6879236800031742189187117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9172315733375656252249489 6879236800031742189187117)
                  ·
                    refine ⟨2579713800011903320945169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6879236800031742189187117 2579713800011903320945169)
                    ·
                      refine ⟨1934785350008927490708877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2579713800011903320945169 1934785350008927490708877)
                      ·
                        rfl

theorem cell23_3767981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_3767981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767981 prefixEnd_3767981 := by exact prefixLift 3767981
  have htrace : WordTrace (prefixWord ++ tailWord_3767981) baseStart_3767981 baseEnd_3767981 := by
    simpa [prefixWord, tailWord_3767981, baseEnd_3767981] using wordTrace_append hprefix tailTrace_3767981
  have hstable : (prefixWord ++ tailWord_3767981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767981).length < 2 ^ (prefixWord ++ tailWord_3767981).sum := by decide
  have hdescent : baseEnd_3767981 < baseStart_3767981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767982 : List Nat := [4, 1, 4, 1, 2, 2, 2, 2, 1, 4]
def baseStart_3767982 : Nat := 118140960795 + 3767982 * 2 ^ 59
def prefixEnd_3767982 : Nat := 4983230072969 + 3 ^ 40 * 3767982 * 2
def baseEnd_3767982 : Nat := 644928621163193995598791

theorem tailTrace_3767982 : CollatzResearch.WordTrace tailWord_3767982 prefixEnd_3767982 644928621163193995598791 := by
  unfold tailWord_3767982
  simp only [CollatzResearch.WordTrace]
  refine ⟨17178699229406526117182275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91619729223501472624972133 17178699229406526117182275)
  ·
    refine ⟨25768048844109789175773413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17178699229406526117182275 25768048844109789175773413)
    ·
      refine ⟨4831509158270585470457515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25768048844109789175773413 4831509158270585470457515)
      ·
        refine ⟨7247263737405878205686273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4831509158270585470457515 7247263737405878205686273)
        ·
          refine ⟨5435447803054408654264705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7247263737405878205686273 5435447803054408654264705)
          ·
            refine ⟨4076585852290806490698529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5435447803054408654264705 4076585852290806490698529)
            ·
              refine ⟨3057439389218104868023897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4076585852290806490698529 3057439389218104868023897)
              ·
                refine ⟨2293079541913578651017923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3057439389218104868023897 2293079541913578651017923)
                ·
                  refine ⟨3439619312870367976526885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293079541913578651017923 3439619312870367976526885)
                  ·
                    refine ⟨644928621163193995598791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3439619312870367976526885 644928621163193995598791)
                    ·
                      rfl

theorem cell23_3767982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_3767982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767982 prefixEnd_3767982 := by exact prefixLift 3767982
  have htrace : WordTrace (prefixWord ++ tailWord_3767982) baseStart_3767982 baseEnd_3767982 := by
    simpa [prefixWord, tailWord_3767982, baseEnd_3767982] using wordTrace_append hprefix tailTrace_3767982
  have hstable : (prefixWord ++ tailWord_3767982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767982).length < 2 ^ (prefixWord ++ tailWord_3767982).sum := by decide
  have hdescent : baseEnd_3767982 < baseStart_3767982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767997 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_3767997 : Nat := 118140960795 + 3767997 * 2 ^ 59
def prefixEnd_3767997 : Nat := 4983230072969 + 3 ^ 40 * 3767997 * 2
def baseEnd_3767997 : Nat := 1934793565699399428108803

theorem tailTrace_3767997 : CollatzResearch.WordTrace tailWord_3767997 prefixEnd_3767997 1934793565699399428108803 := by
  unfold tailWord_3767997
  simp only [CollatzResearch.WordTrace]
  refine ⟨137430140930197866499254245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91620093953465244332836163 137430140930197866499254245)
  ·
    refine ⟨25768151424412099968610171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137430140930197866499254245 25768151424412099968610171)
    ·
      refine ⟨38652227136618149952915257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25768151424412099968610171 38652227136618149952915257)
      ·
        refine ⟨28989170352463612464686443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38652227136618149952915257 28989170352463612464686443)
        ·
          refine ⟨43483755528695418697029665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28989170352463612464686443 43483755528695418697029665)
          ·
            refine ⟨32612816646521564022772249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43483755528695418697029665 32612816646521564022772249)
            ·
              refine ⟨24459612484891173017079187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32612816646521564022772249 24459612484891173017079187)
              ·
                refine ⟨36689418727336759525618781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24459612484891173017079187 36689418727336759525618781)
                ·
                  refine ⟨13758532022751284822107043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36689418727336759525618781 13758532022751284822107043)
                  ·
                    refine ⟨20637798034126927233160565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13758532022751284822107043 20637798034126927233160565)
                    ·
                      refine ⟨1934793565699399428108803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20637798034126927233160565 1934793565699399428108803)
                      ·
                        rfl

theorem cell23_3767997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_3767997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3767997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3767997 prefixEnd_3767997 := by exact prefixLift 3767997
  have htrace : WordTrace (prefixWord ++ tailWord_3767997) baseStart_3767997 baseEnd_3767997 := by
    simpa [prefixWord, tailWord_3767997, baseEnd_3767997] using wordTrace_append hprefix tailTrace_3767997
  have hstable : (prefixWord ++ tailWord_3767997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767997).length < 2 ^ (prefixWord ++ tailWord_3767997).sum := by decide
  have hdescent : baseEnd_3767997 < baseStart_3767997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768004 : List Nat := [2, 3, 3, 1, 1, 1, 4, 1, 1, 6]
def baseStart_3768004 : Nat := 118140960795 + 3768004 * 2 ^ 59
def prefixEnd_3768004 : Nat := 4983230072969 + 3 ^ 40 * 3768004 * 2
def baseEnd_3768004 : Nat := 644932386687993633573757

theorem tailTrace_3768004 : CollatzResearch.WordTrace tailWord_3768004 prefixEnd_3768004 644932386687993633573757 := by
  unfold tailWord_3768004
  simp only [CollatzResearch.WordTrace]
  refine ⟨68715198120586253347379533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91620264160781671129839377 68715198120586253347379533)
  ·
    refine ⟨25768199295219845005267325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68715198120586253347379533 25768199295219845005267325)
    ·
      refine ⟨9663074735707441876975247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25768199295219845005267325 9663074735707441876975247)
      ·
        refine ⟨14494612103561162815462871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9663074735707441876975247 14494612103561162815462871)
        ·
          refine ⟨21741918155341744223194307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14494612103561162815462871 21741918155341744223194307)
          ·
            refine ⟨32612877233012616334791461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21741918155341744223194307 32612877233012616334791461)
            ·
              refine ⟨6114914481189865562773399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32612877233012616334791461 6114914481189865562773399)
              ·
                refine ⟨9172371721784798344160099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6114914481189865562773399 9172371721784798344160099)
                ·
                  refine ⟨13758557582677197516240149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9172371721784798344160099 13758557582677197516240149)
                  ·
                    refine ⟨644932386687993633573757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13758557582677197516240149 644932386687993633573757)
                    ·
                      rfl

theorem cell23_3768004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_3768004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768004 prefixEnd_3768004 := by exact prefixLift 3768004
  have htrace : WordTrace (prefixWord ++ tailWord_3768004) baseStart_3768004 baseEnd_3768004 := by
    simpa [prefixWord, tailWord_3768004, baseEnd_3768004] using wordTrace_append hprefix tailTrace_3768004
  have hstable : (prefixWord ++ tailWord_3768004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768004).length < 2 ^ (prefixWord ++ tailWord_3768004).sum := by decide
  have hdescent : baseEnd_3768004 < baseStart_3768004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768014 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3]
def baseStart_3768014 : Nat := 118140960795 + 3768014 * 2 ^ 59
def prefixEnd_3768014 : Nat := 4983230072969 + 3 ^ 40 * 3768014 * 2
def baseEnd_3768014 : Nat := 1934802294870525861596225

theorem tailTrace_3768014 : CollatzResearch.WordTrace tailWord_3768014 prefixEnd_3768014 1934802294870525861596225 := by
  unfold tailWord_3768014
  simp only [CollatzResearch.WordTrace]
  refine ⟨17178845121392034800327887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91620507314090852268415397 17178845121392034800327887)
  ·
    refine ⟨25768267682088052200491831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17178845121392034800327887 25768267682088052200491831)
    ·
      refine ⟨38652401523132078300737747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25768267682088052200491831 38652401523132078300737747)
      ·
        refine ⟨57978602284698117451106621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38652401523132078300737747 57978602284698117451106621)
        ·
          refine ⟨21741975856761794044164983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57978602284698117451106621 21741975856761794044164983)
          ·
            refine ⟨32612963785142691066247475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21741975856761794044164983 32612963785142691066247475)
            ·
              refine ⟨48919445677714036599371213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32612963785142691066247475 48919445677714036599371213)
              ·
                refine ⟨18344792129142763724764205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48919445677714036599371213 18344792129142763724764205)
                ·
                  refine ⟨6879297048428536396786577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18344792129142763724764205 6879297048428536396786577)
                  ·
                    refine ⟨5159472786321402297589933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6879297048428536396786577 5159472786321402297589933)
                    ·
                      refine ⟨1934802294870525861596225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5159472786321402297589933 1934802294870525861596225)
                      ·
                        rfl

theorem cell23_3768014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_3768014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768014 prefixEnd_3768014 := by exact prefixLift 3768014
  have htrace : WordTrace (prefixWord ++ tailWord_3768014) baseStart_3768014 baseEnd_3768014 := by
    simpa [prefixWord, tailWord_3768014, baseEnd_3768014] using wordTrace_append hprefix tailTrace_3768014
  have hstable : (prefixWord ++ tailWord_3768014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768014).length < 2 ^ (prefixWord ++ tailWord_3768014).sum := by decide
  have hdescent : baseEnd_3768014 < baseStart_3768014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768028 : List Nat := [2, 2, 5, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_3768028 : Nat := 118140960795 + 3768028 * 2 ^ 59
def prefixEnd_3768028 : Nat := 4983230072969 + 3 ^ 40 * 3768028 * 2
def baseEnd_3768028 : Nat := 1934809483599688806821161

theorem tailTrace_3768028 : CollatzResearch.WordTrace tailWord_3768028 prefixEnd_3768028 1934809483599688806821161 := by
  unfold tailWord_3768028
  simp only [CollatzResearch.WordTrace]
  refine ⟨68715635796542779396816369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91620847728723705862421825 68715635796542779396816369)
  ·
    refine ⟨51536726847407084547612277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68715635796542779396816369 51536726847407084547612277)
    ·
      refine ⟨4831568141944414176338651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51536726847407084547612277 4831568141944414176338651)
      ·
        refine ⟨7247352212916621264507977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4831568141944414176338651 7247352212916621264507977)
        ·
          refine ⟨5435514159687465948380983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7247352212916621264507977 5435514159687465948380983)
          ·
            refine ⟨8153271239531198922571475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5435514159687465948380983 8153271239531198922571475)
            ·
              refine ⟨12229906859296798383857213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8153271239531198922571475 12229906859296798383857213)
              ·
                refine ⟨4586215072236299393946455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12229906859296798383857213 4586215072236299393946455)
                ·
                  refine ⟨6879322608354449090919683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4586215072236299393946455 6879322608354449090919683)
                  ·
                    refine ⟨10318983912531673636379525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6879322608354449090919683 10318983912531673636379525)
                    ·
                      refine ⟨1934809483599688806821161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10318983912531673636379525 1934809483599688806821161)
                      ·
                        rfl

theorem cell23_3768028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_3768028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768028 prefixEnd_3768028 := by exact prefixLift 3768028
  have htrace : WordTrace (prefixWord ++ tailWord_3768028) baseStart_3768028 baseEnd_3768028 := by
    simpa [prefixWord, tailWord_3768028, baseEnd_3768028] using wordTrace_append hprefix tailTrace_3768028
  have hstable : (prefixWord ++ tailWord_3768028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768028).length < 2 ^ (prefixWord ++ tailWord_3768028).sum := by decide
  have hdescent : baseEnd_3768028 < baseStart_3768028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768045 : List Nat := [1, 5, 1, 2, 1, 2, 2, 4, 1, 2, 2]
def baseStart_3768045 : Nat := 118140960795 + 3768045 * 2 ^ 59
def prefixEnd_3768045 : Nat := 4983230072969 + 3 ^ 40 * 3768045 * 2
def baseEnd_3768045 : Nat := 1934818212770815240308583

theorem tailTrace_3768045 : CollatzResearch.WordTrace tailWord_3768045 prefixEnd_3768045 1934818212770815240308583 := by
  unfold tailWord_3768045
  simp only [CollatzResearch.WordTrace]
  refine ⟨137431891634023970697001589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91621261089349313798001059 137431891634023970697001589)
  ·
    refine ⟨12884239840689747252843899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137431891634023970697001589 12884239840689747252843899)
    ·
      refine ⟨19326359761034620879265849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12884239840689747252843899 19326359761034620879265849)
      ·
        refine ⟨14494769820775965659449387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19326359761034620879265849 14494769820775965659449387)
        ·
          refine ⟨21742154731163948489174081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14494769820775965659449387 21742154731163948489174081)
          ·
            refine ⟨16306616048372961366880561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21742154731163948489174081 16306616048372961366880561)
            ·
              refine ⟨12229962036279721025160421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16306616048372961366880561 12229962036279721025160421)
              ·
                refine ⟨2293117881802447692217579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12229962036279721025160421 2293117881802447692217579)
                ·
                  refine ⟨3439676822703671538326369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293117881802447692217579 3439676822703671538326369)
                  ·
                    refine ⟨2579757617027753653744777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3439676822703671538326369 2579757617027753653744777)
                    ·
                      refine ⟨1934818212770815240308583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2579757617027753653744777 1934818212770815240308583)
                      ·
                        rfl

theorem cell23_3768045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_3768045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768045 prefixEnd_3768045 := by exact prefixLift 3768045
  have htrace : WordTrace (prefixWord ++ tailWord_3768045) baseStart_3768045 baseEnd_3768045 := by
    simpa [prefixWord, tailWord_3768045, baseEnd_3768045] using wordTrace_append hprefix tailTrace_3768045
  have hstable : (prefixWord ++ tailWord_3768045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768045).length < 2 ^ (prefixWord ++ tailWord_3768045).sum := by decide
  have hdescent : baseEnd_3768045 < baseStart_3768045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768067 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 4]
def baseStart_3768067 : Nat := 118140960795 + 3768067 * 2 ^ 59
def prefixEnd_3768067 : Nat := 4983230072969 + 3 ^ 40 * 3768067 * 2
def baseEnd_3768067 : Nat := 1934829509345214154233481

theorem tailTrace_3768067 : CollatzResearch.WordTrace tailWord_3768067 prefixEnd_3768067 1934829509345214154233481 := by
  unfold tailWord_3768067
  simp only [CollatzResearch.WordTrace]
  refine ⟨137432694039944268454302455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91621796026629512302868303 137432694039944268454302455)
  ·
    refine ⟨206149041059916402681453683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137432694039944268454302455 206149041059916402681453683)
    ·
      refine ⟨309223561589874604022180525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206149041059916402681453683 309223561589874604022180525)
      ·
        refine ⟨115958835596202976508317697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309223561589874604022180525 115958835596202976508317697)
        ·
          refine ⟨86969126697152232381238273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115958835596202976508317697 86969126697152232381238273)
          ·
            refine ⟨65226845022864174285928705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86969126697152232381238273 65226845022864174285928705)
            ·
              refine ⟨48920133767148130714446529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65226845022864174285928705 48920133767148130714446529)
              ·
                refine ⟨36690100325361098035834897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48920133767148130714446529 36690100325361098035834897)
                ·
                  refine ⟨27517575244020823526876173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36690100325361098035834897 27517575244020823526876173)
                  ·
                    refine ⟨10319090716507808822578565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27517575244020823526876173 10319090716507808822578565)
                    ·
                      refine ⟨1934829509345214154233481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10319090716507808822578565 1934829509345214154233481)
                      ·
                        rfl

theorem cell23_3768067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_3768067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768067 prefixEnd_3768067 := by exact prefixLift 3768067
  have htrace : WordTrace (prefixWord ++ tailWord_3768067) baseStart_3768067 baseEnd_3768067 := by
    simpa [prefixWord, tailWord_3768067, baseEnd_3768067] using wordTrace_append hprefix tailTrace_3768067
  have hstable : (prefixWord ++ tailWord_3768067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768067).length < 2 ^ (prefixWord ++ tailWord_3768067).sum := by decide
  have hdescent : baseEnd_3768067 < baseStart_3768067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768154 : List Nat := [3, 1, 1, 2, 1, 3, 1, 4, 2, 5]
def baseStart_3768154 : Nat := 118140960795 + 3768154 * 2 ^ 59
def prefixEnd_3768154 : Nat := 4983230072969 + 3 ^ 40 * 3768154 * 2
def baseEnd_3768154 : Nat := 644958060720718437948527

theorem tailTrace_3768154 : CollatzResearch.WordTrace tailWord_3768154 prefixEnd_3768154 644958060720718437948527 := by
  unfold tailWord_3768154
  simp only [CollatzResearch.WordTrace]
  refine ⟨34358966797657270578179879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91623911460419388208479677 34358966797657270578179879)
  ·
    refine ⟨51538450196485905867269819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34358966797657270578179879 51538450196485905867269819)
    ·
      refine ⟨77307675294728858800904729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51538450196485905867269819 77307675294728858800904729)
      ·
        refine ⟨57980756471046644100678547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77307675294728858800904729 57980756471046644100678547)
        ·
          refine ⟨86971134706569966151017821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57980756471046644100678547 86971134706569966151017821)
          ·
            refine ⟨32614175514963737306631683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86971134706569966151017821 32614175514963737306631683)
            ·
              refine ⟨48921263272445605959947525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32614175514963737306631683 48921263272445605959947525)
              ·
                refine ⟨9172736863583551117490161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48921263272445605959947525 9172736863583551117490161)
                ·
                  refine ⟨6879552647687663338117621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9172736863583551117490161 6879552647687663338117621)
                  ·
                    refine ⟨644958060720718437948527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6879552647687663338117621 644958060720718437948527)
                    ·
                      rfl

theorem cell23_3768154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_3768154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768154 prefixEnd_3768154 := by exact prefixLift 3768154
  have htrace : WordTrace (prefixWord ++ tailWord_3768154) baseStart_3768154 baseEnd_3768154 := by
    simpa [prefixWord, tailWord_3768154, baseEnd_3768154] using wordTrace_append hprefix tailTrace_3768154
  have hstable : (prefixWord ++ tailWord_3768154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768154).length < 2 ^ (prefixWord ++ tailWord_3768154).sum := by decide
  have hdescent : baseEnd_3768154 < baseStart_3768154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768218 : List Nat := [3, 1, 1, 4, 2, 2, 2, 1, 3, 4]
def baseStart_3768218 : Nat := 118140960795 + 3768218 * 2 ^ 59
def prefixEnd_3768218 : Nat := 4983230072969 + 3 ^ 40 * 3768218 * 2
def baseEnd_3768218 : Nat := 644969014974681021148429

theorem tailTrace_3768218 : CollatzResearch.WordTrace tailWord_3768218 prefixEnd_3768218 644969014974681021148429 := by
  unfold tailWord_3768218
  simp only [CollatzResearch.WordTrace]
  refine ⟨34359550365599305310762327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91625467641598147495366205 34359550365599305310762327)
  ·
    refine ⟨51539325548398957966143491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34359550365599305310762327 51539325548398957966143491)
    ·
      refine ⟨77308988322598436949215237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51539325548398957966143491 77308988322598436949215237)
      ·
        refine ⟨14495435310487206927977857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77308988322598436949215237 14495435310487206927977857)
        ·
          refine ⟨10871576482865405195983393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14495435310487206927977857 10871576482865405195983393)
          ·
            refine ⟨8153682362149053896987545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10871576482865405195983393 8153682362149053896987545)
            ·
              refine ⟨6115261771611790422740659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8153682362149053896987545 6115261771611790422740659)
              ·
                refine ⟨9172892657417685634110989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6115261771611790422740659 9172892657417685634110989)
                ·
                  refine ⟨3439834746531632112791621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9172892657417685634110989 3439834746531632112791621)
                  ·
                    refine ⟨644969014974681021148429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3439834746531632112791621 644969014974681021148429)
                    ·
                      rfl

theorem cell23_3768218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_3768218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768218 prefixEnd_3768218 := by exact prefixLift 3768218
  have htrace : WordTrace (prefixWord ++ tailWord_3768218) baseStart_3768218 baseEnd_3768218 := by
    simpa [prefixWord, tailWord_3768218, baseEnd_3768218] using wordTrace_append hprefix tailTrace_3768218
  have hstable : (prefixWord ++ tailWord_3768218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768218).length < 2 ^ (prefixWord ++ tailWord_3768218).sum := by decide
  have hdescent : baseEnd_3768218 < baseStart_3768218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768268 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 4, 3, 2]
def baseStart_3768268 : Nat := 118140960795 + 3768268 * 2 ^ 59
def prefixEnd_3768268 : Nat := 4983230072969 + 3 ^ 40 * 3768268 * 2
def baseEnd_3768268 : Nat := 1934932718956767867820057

theorem tailTrace_3768268 : CollatzResearch.WordTrace tailWord_3768268 prefixEnd_3768268 1934932718956767867820057 := by
  unfold tailWord_3768268
  simp only [CollatzResearch.WordTrace]
  refine ⟨68720012556108039891184729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91626683408144053188246305 68720012556108039891184729)
  ·
    refine ⟨51540009417081029918388547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68720012556108039891184729 51540009417081029918388547)
    ·
      refine ⟨77310014125621544877582821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51540009417081029918388547 77310014125621544877582821)
      ·
        refine ⟨14495627648554039664546779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77310014125621544877582821 14495627648554039664546779)
        ·
          refine ⟨21743441472831059496820169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14495627648554039664546779 21743441472831059496820169)
          ·
            refine ⟨16307581104623294622615127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21743441472831059496820169 16307581104623294622615127)
            ·
              refine ⟨24461371656934941933922691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16307581104623294622615127 24461371656934941933922691)
              ·
                refine ⟨36692057485402412900884037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24461371656934941933922691 36692057485402412900884037)
                ·
                  refine ⟨6879760778512952418915757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36692057485402412900884037 6879760778512952418915757)
                  ·
                    refine ⟨2579910291942357157093409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6879760778512952418915757 2579910291942357157093409)
                    ·
                      refine ⟨1934932718956767867820057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2579910291942357157093409 1934932718956767867820057)
                      ·
                        rfl

theorem cell23_3768268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_3768268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768268 prefixEnd_3768268 := by exact prefixLift 3768268
  have htrace : WordTrace (prefixWord ++ tailWord_3768268) baseStart_3768268 baseEnd_3768268 := by
    simpa [prefixWord, tailWord_3768268, baseEnd_3768268] using wordTrace_append hprefix tailTrace_3768268
  have hstable : (prefixWord ++ tailWord_3768268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768268).length < 2 ^ (prefixWord ++ tailWord_3768268).sum := by decide
  have hdescent : baseEnd_3768268 < baseStart_3768268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768295 : List Nat := [1, 1, 5, 2, 3, 2, 1, 2, 1, 5]
def baseStart_3768295 : Nat := 118140960795 + 3768295 * 2 ^ 59
def prefixEnd_3768295 : Nat := 4983230072969 + 3 ^ 40 * 3768295 * 2
def baseEnd_3768295 : Nat := 644982194311479754060811

theorem tailTrace_3768295 : CollatzResearch.WordTrace tailWord_3768295 prefixEnd_3768295 644982194311479754060811 := by
  unfold tailWord_3768295
  simp only [CollatzResearch.WordTrace]
  refine ⟨137441009883118263393602339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91627339922078842262401559 137441009883118263393602339)
  ·
    refine ⟨206161514824677395090403509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137441009883118263393602339 206161514824677395090403509)
    ·
      refine ⟨19327642014813505789725329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206161514824677395090403509 19327642014813505789725329)
      ·
        refine ⟨14495731511110129342293997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19327642014813505789725329 14495731511110129342293997)
        ·
          refine ⟨5435899316666298503360249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14495731511110129342293997 5435899316666298503360249)
          ·
            refine ⟨4076924487499723877520187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5435899316666298503360249 4076924487499723877520187)
            ·
              refine ⟨6115386731249585816280281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4076924487499723877520187 6115386731249585816280281)
              ·
                refine ⟨4586540048437189362210211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6115386731249585816280281 4586540048437189362210211)
                ·
                  refine ⟨6879810072655784043315317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4586540048437189362210211 6879810072655784043315317)
                  ·
                    refine ⟨644982194311479754060811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6879810072655784043315317 644982194311479754060811)
                    ·
                      rfl

theorem cell23_3768295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_3768295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768295 prefixEnd_3768295 := by exact prefixLift 3768295
  have htrace : WordTrace (prefixWord ++ tailWord_3768295) baseStart_3768295 baseEnd_3768295 := by
    simpa [prefixWord, tailWord_3768295, baseEnd_3768295] using wordTrace_append hprefix tailTrace_3768295
  have hstable : (prefixWord ++ tailWord_3768295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768295).length < 2 ^ (prefixWord ++ tailWord_3768295).sum := by decide
  have hdescent : baseEnd_3768295 < baseStart_3768295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768304 : List Nat := [2, 1, 1, 1, 3, 2, 4, 9]
def baseStart_3768304 : Nat := 118140960795 + 3768304 * 2 ^ 59
def prefixEnd_3768304 : Nat := 4983230072969 + 3 ^ 40 * 3768304 * 2
def baseEnd_3768304 : Nat := 71664859417049249147033

theorem tailTrace_3768304 : CollatzResearch.WordTrace tailWord_3768304 prefixEnd_3768304 71664859417049249147033 := by
  unfold tailWord_3768304
  simp only [CollatzResearch.WordTrace]
  refine ⟨68720669070042828965339983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91627558760057105287119977 68720669070042828965339983)
  ·
    refine ⟨103081003605064243448009975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68720669070042828965339983 103081003605064243448009975)
    ·
      refine ⟨154621505407596365172014963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103081003605064243448009975 154621505407596365172014963)
      ·
        refine ⟨231932258111394547758022445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154621505407596365172014963 231932258111394547758022445)
        ·
          refine ⟨86974596791772955409258417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231932258111394547758022445 86974596791772955409258417)
          ·
            refine ⟨65230947593829716556943813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86974596791772955409258417 65230947593829716556943813)
            ·
              refine ⟨12230802673843071854426965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65230947593829716556943813 12230802673843071854426965)
              ·
                refine ⟨71664859417049249147033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12230802673843071854426965 71664859417049249147033)
                ·
                  rfl

theorem cell23_3768304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 9].length) (baseStart_3768304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768304 prefixEnd_3768304 := by exact prefixLift 3768304
  have htrace : WordTrace (prefixWord ++ tailWord_3768304) baseStart_3768304 baseEnd_3768304 := by
    simpa [prefixWord, tailWord_3768304, baseEnd_3768304] using wordTrace_append hprefix tailTrace_3768304
  have hstable : (prefixWord ++ tailWord_3768304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768304).length < 2 ^ (prefixWord ++ tailWord_3768304).sum := by decide
  have hdescent : baseEnd_3768304 < baseStart_3768304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768331 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 3]
def baseStart_3768331 : Nat := 118140960795 + 3768331 * 2 ^ 59
def prefixEnd_3768331 : Nat := 4983230072969 + 3 ^ 40 * 3768331 * 2
def baseEnd_3768331 : Nat := 1934965068238001121332267

theorem tailTrace_3768331 : CollatzResearch.WordTrace tailWord_3768331 prefixEnd_3768331 1934965068238001121332267 := by
  unfold tailWord_3768331
  simp only [CollatzResearch.WordTrace]
  refine ⟨137442322910987841541912847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91628215273991894361275231 137442322910987841541912847)
  ·
    refine ⟨206163484366481762312869271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137442322910987841541912847 206163484366481762312869271)
    ·
      refine ⟨309245226549722643469303907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206163484366481762312869271 309245226549722643469303907)
      ·
        refine ⟨463867839824583965203955861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309245226549722643469303907 463867839824583965203955861)
        ·
          refine ⟨21743804991777373368935431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 463867839824583965203955861 21743804991777373368935431)
          ·
            refine ⟨32615707487666060053403147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21743804991777373368935431 32615707487666060053403147)
            ·
              refine ⟨48923561231499090080104721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32615707487666060053403147 48923561231499090080104721)
              ·
                refine ⟨36692670923624317560078541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48923561231499090080104721 36692670923624317560078541)
                ·
                  refine ⟨13759751596359119085029453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36692670923624317560078541 13759751596359119085029453)
                  ·
                    refine ⟨5159906848634669656886045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13759751596359119085029453 5159906848634669656886045)
                    ·
                      refine ⟨1934965068238001121332267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5159906848634669656886045 1934965068238001121332267)
                      ·
                        rfl

theorem cell23_3768331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 3].length) (baseStart_3768331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768331 prefixEnd_3768331 := by exact prefixLift 3768331
  have htrace : WordTrace (prefixWord ++ tailWord_3768331) baseStart_3768331 baseEnd_3768331 := by
    simpa [prefixWord, tailWord_3768331, baseEnd_3768331] using wordTrace_append hprefix tailTrace_3768331
  have hstable : (prefixWord ++ tailWord_3768331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768331).length < 2 ^ (prefixWord ++ tailWord_3768331).sum := by decide
  have hdescent : baseEnd_3768331 < baseStart_3768331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768332 : List Nat := [2, 2, 1, 2, 3, 1, 3, 4, 1, 2, 2]
def baseStart_3768332 : Nat := 118140960795 + 3768332 * 2 ^ 59
def prefixEnd_3768332 : Nat := 4983230072969 + 3 ^ 40 * 3768332 * 2
def baseEnd_3768332 : Nat := 1934965581718655617419763

theorem tailTrace_3768332 : CollatzResearch.WordTrace tailWord_3768332 prefixEnd_3768332 1934965581718655617419763 := by
  unfold tailWord_3768332
  simp only [CollatzResearch.WordTrace]
  refine ⟨68721179691992109356349625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91628239589322812475132833 68721179691992109356349625)
  ·
    refine ⟨51540884768994082017262219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68721179691992109356349625 51540884768994082017262219)
    ·
      refine ⟨77311327153491123025893329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51540884768994082017262219 77311327153491123025893329)
      ·
        refine ⟨57983495365118342269419997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77311327153491123025893329 57983495365118342269419997)
        ·
          refine ⟨21743810761919378351032499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57983495365118342269419997 21743810761919378351032499)
          ·
            refine ⟨32615716142879067526548749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21743810761919378351032499 32615716142879067526548749)
            ·
              refine ⟨12230893553579650322455781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32615716142879067526548749 12230893553579650322455781)
              ·
                refine ⟨2293292541296184435460459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12230893553579650322455781 2293292541296184435460459)
                ·
                  refine ⟨3439938811944276653190689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293292541296184435460459 3439938811944276653190689)
                  ·
                    refine ⟨2579954108958207489893017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3439938811944276653190689 2579954108958207489893017)
                    ·
                      refine ⟨1934965581718655617419763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2579954108958207489893017 1934965581718655617419763)
                      ·
                        rfl

theorem cell23_3768332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_3768332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768332 prefixEnd_3768332 := by exact prefixLift 3768332
  have htrace : WordTrace (prefixWord ++ tailWord_3768332) baseStart_3768332 baseEnd_3768332 := by
    simpa [prefixWord, tailWord_3768332, baseEnd_3768332] using wordTrace_append hprefix tailTrace_3768332
  have hstable : (prefixWord ++ tailWord_3768332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768332).length < 2 ^ (prefixWord ++ tailWord_3768332).sum := by decide
  have hdescent : baseEnd_3768332 < baseStart_3768332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768348 : List Nat := [2, 2, 3, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_3768348 : Nat := 118140960795 + 3768348 * 2 ^ 59
def prefixEnd_3768348 : Nat := 4983230072969 + 3 ^ 40 * 3768348 * 2
def baseEnd_3768348 : Nat := 1934973797409127554819689

theorem tailTrace_3768348 : CollatzResearch.WordTrace tailWord_3768348 prefixEnd_3768348 1934973797409127554819689 := by
  unfold tailWord_3768348
  simp only [CollatzResearch.WordTrace]
  refine ⟨68721471475963126722640849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91628628634617502296854465 68721471475963126722640849)
  ·
    refine ⟨51541103606972345041980637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68721471475963126722640849 51541103606972345041980637)
    ·
      refine ⟨19327913852614629390742739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51541103606972345041980637 19327913852614629390742739)
      ·
        refine ⟨28991870778921944086114109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19327913852614629390742739 28991870778921944086114109)
        ·
          refine ⟨10871951542095729032292791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28991870778921944086114109 10871951542095729032292791)
          ·
            refine ⟨16307927313143593548439187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10871951542095729032292791 16307927313143593548439187)
            ·
              refine ⟨24461890969715390322658781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16307927313143593548439187 24461890969715390322658781)
              ·
                refine ⟨9173209113643271370997043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24461890969715390322658781 9173209113643271370997043)
                ·
                  refine ⟨13759813670464907056495565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9173209113643271370997043 13759813670464907056495565)
                  ·
                    refine ⟨5159930126424340146185837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13759813670464907056495565 5159930126424340146185837)
                    ·
                      refine ⟨1934973797409127554819689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5159930126424340146185837 1934973797409127554819689)
                      ·
                        rfl

theorem cell23_3768348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_3768348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768348 prefixEnd_3768348 := by exact prefixLift 3768348
  have htrace : WordTrace (prefixWord ++ tailWord_3768348) baseStart_3768348 baseEnd_3768348 := by
    simpa [prefixWord, tailWord_3768348, baseEnd_3768348] using wordTrace_append hprefix tailTrace_3768348
  have hstable : (prefixWord ++ tailWord_3768348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768348).length < 2 ^ (prefixWord ++ tailWord_3768348).sum := by decide
  have hdescent : baseEnd_3768348 < baseStart_3768348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768381 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 4, 6]
def baseStart_3768381 : Nat := 118140960795 + 3768381 * 2 ^ 59
def prefixEnd_3768381 : Nat := 4983230072969 + 3 ^ 40 * 3768381 * 2
def baseEnd_3768381 : Nat := 644996914090241975235679

theorem tailTrace_3768381 : CollatzResearch.WordTrace tailWord_3768381 prefixEnd_3768381 644996914090241975235679 := by
  unfold tailWord_3768381
  simp only [CollatzResearch.WordTrace]
  refine ⟨137444146560806700081232997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91629431040537800054155331 137444146560806700081232997)
  ·
    refine ⟨25770777480151256265231187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137444146560806700081232997 25770777480151256265231187)
    ·
      refine ⟨38656166220226884397846781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25770777480151256265231187 38656166220226884397846781)
      ·
        refine ⟨14496062332585081649192543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38656166220226884397846781 14496062332585081649192543)
        ·
          refine ⟨21744093498877622473788815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14496062332585081649192543 21744093498877622473788815)
          ·
            refine ⟨32616140248316433710683223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21744093498877622473788815 32616140248316433710683223)
            ·
              refine ⟨48924210372474650566024835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32616140248316433710683223 48924210372474650566024835)
              ·
                refine ⟨73386315558711975849037253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48924210372474650566024835 73386315558711975849037253)
                ·
                  refine ⟨13759934167258495471694485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73386315558711975849037253 13759934167258495471694485)
                  ·
                    refine ⟨644996914090241975235679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13759934167258495471694485 644996914090241975235679)
                    ·
                      rfl

theorem cell23_3768381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_3768381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768381 prefixEnd_3768381 := by exact prefixLift 3768381
  have htrace : WordTrace (prefixWord ++ tailWord_3768381) baseStart_3768381 baseEnd_3768381 := by
    simpa [prefixWord, tailWord_3768381, baseEnd_3768381] using wordTrace_append hprefix tailTrace_3768381
  have hstable : (prefixWord ++ tailWord_3768381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768381).length < 2 ^ (prefixWord ++ tailWord_3768381).sum := by decide
  have hdescent : baseEnd_3768381 < baseStart_3768381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768382 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_3768382 : Nat := 118140960795 + 3768382 * 2 ^ 59
def prefixEnd_3768382 : Nat := 4983230072969 + 3 ^ 40 * 3768382 * 2
def baseEnd_3768382 : Nat := 1934991255751380421794533

theorem tailTrace_3768382 : CollatzResearch.WordTrace tailWord_3768382 prefixEnd_3768382 1934991255751380421794533 := by
  unfold tailWord_3768382
  simp only [CollatzResearch.WordTrace]
  refine ⟨17180522879225384656502425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91629455355868718168012933 17180522879225384656502425)
  ·
    refine ⟨12885392159419038492376819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17180522879225384656502425 12885392159419038492376819)
    ·
      refine ⟨19328088239128557738565229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12885392159419038492376819 19328088239128557738565229)
      ·
        refine ⟨7248033089673209151961961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19328088239128557738565229 7248033089673209151961961)
        ·
          refine ⟨5436024817254906863971471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7248033089673209151961961 5436024817254906863971471)
          ·
            refine ⟨8154037225882360295957207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5436024817254906863971471 8154037225882360295957207)
            ·
              refine ⟨12231055838823540443935811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8154037225882360295957207 12231055838823540443935811)
              ·
                refine ⟨18346583758235310665903717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12231055838823540443935811 18346583758235310665903717)
                ·
                  refine ⟨3439984454669120749856947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18346583758235310665903717 3439984454669120749856947)
                  ·
                    refine ⟨5159976682003681124785421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3439984454669120749856947 5159976682003681124785421)
                    ·
                      refine ⟨1934991255751380421794533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5159976682003681124785421 1934991255751380421794533)
                      ·
                        rfl

theorem cell23_3768382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_3768382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768382 prefixEnd_3768382 := by exact prefixLift 3768382
  have htrace : WordTrace (prefixWord ++ tailWord_3768382) baseStart_3768382 baseEnd_3768382 := by
    simpa [prefixWord, tailWord_3768382, baseEnd_3768382] using wordTrace_append hprefix tailTrace_3768382
  have hstable : (prefixWord ++ tailWord_3768382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768382).length < 2 ^ (prefixWord ++ tailWord_3768382).sum := by decide
  have hdescent : baseEnd_3768382 < baseStart_3768382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768405 : List Nat := [1, 3, 2, 2, 1, 3, 3, 1, 1, 4, 2]
def baseStart_3768405 : Nat := 118140960795 + 3768405 * 2 ^ 59
def prefixEnd_3768405 : Nat := 4983230072969 + 3 ^ 40 * 3768405 * 2
def baseEnd_3768405 : Nat := 1935003065806433831806927

theorem tailTrace_3768405 : CollatzResearch.WordTrace tailWord_3768405 prefixEnd_3768405 1935003065806433831806927 := by
  unfold tailWord_3768405
  simp only [CollatzResearch.WordTrace]
  refine ⟨137445021912719752180106669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91630014608479834786737779 137445021912719752180106669)
  ·
    refine ⟨51541883217269907067540001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137445021912719752180106669 51541883217269907067540001)
    ·
      refine ⟨38656412412952430300655001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51541883217269907067540001 38656412412952430300655001)
      ·
        refine ⟨28992309309714322725491251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38656412412952430300655001 28992309309714322725491251)
        ·
          refine ⟨43488463964571484088236877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28992309309714322725491251 43488463964571484088236877)
          ·
            refine ⟨16308173986714306533088829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43488463964571484088236877 16308173986714306533088829)
            ·
              refine ⟨6115565245017864949908311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16308173986714306533088829 6115565245017864949908311)
              ·
                refine ⟨9173347867526797424862467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6115565245017864949908311 9173347867526797424862467)
                ·
                  refine ⟨13760021801290196137293701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9173347867526797424862467 13760021801290196137293701)
                  ·
                    refine ⟨2580004087741911775742569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13760021801290196137293701 2580004087741911775742569)
                    ·
                      refine ⟨1935003065806433831806927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2580004087741911775742569 1935003065806433831806927)
                      ·
                        rfl

theorem cell23_3768405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_3768405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768405 prefixEnd_3768405 := by exact prefixLift 3768405
  have htrace : WordTrace (prefixWord ++ tailWord_3768405) baseStart_3768405 baseEnd_3768405 := by
    simpa [prefixWord, tailWord_3768405, baseEnd_3768405] using wordTrace_append hprefix tailTrace_3768405
  have hstable : (prefixWord ++ tailWord_3768405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768405).length < 2 ^ (prefixWord ++ tailWord_3768405).sum := by decide
  have hdescent : baseEnd_3768405 < baseStart_3768405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768448 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 2, 5, 2]
def baseStart_3768448 : Nat := 118140960795 + 3768448 * 2 ^ 59
def prefixEnd_3768448 : Nat := 4983230072969 + 3 ^ 40 * 3768448 * 2
def baseEnd_3768448 : Nat := 1935025145474577163569229

theorem tailTrace_3768448 : CollatzResearch.WordTrace tailWord_3768448 prefixEnd_3768448 1935025145474577163569229 := by
  unfold tailWord_3768448
  simp only [CollatzResearch.WordTrace]
  refine ⟨68723295125781985261960999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91631060167709313682614665 68723295125781985261960999)
  ·
    refine ⟨103084942688672977892941499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68723295125781985261960999 103084942688672977892941499)
    ·
      refine ⟨154627414033009466839412249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103084942688672977892941499 154627414033009466839412249)
      ·
        refine ⟨115970560524757100129559187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154627414033009466839412249 115970560524757100129559187)
        ·
          refine ⟨173955840787135650194338781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115970560524757100129559187 173955840787135650194338781)
          ·
            refine ⟨65233440295175868822877043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173955840787135650194338781 65233440295175868822877043)
            ·
              refine ⟨97850160442763803234315565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65233440295175868822877043 97850160442763803234315565)
              ·
                refine ⟨36693810166036426212868337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97850160442763803234315565 36693810166036426212868337)
                ·
                  refine ⟨27520357624527319659651253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36693810166036426212868337 27520357624527319659651253)
                  ·
                    refine ⟨2580033527299436218092305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27520357624527319659651253 2580033527299436218092305)
                    ·
                      refine ⟨1935025145474577163569229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2580033527299436218092305 1935025145474577163569229)
                      ·
                        rfl

theorem cell23_3768448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2, 5, 2].length) (baseStart_3768448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768448 prefixEnd_3768448 := by exact prefixLift 3768448
  have htrace : WordTrace (prefixWord ++ tailWord_3768448) baseStart_3768448 baseEnd_3768448 := by
    simpa [prefixWord, tailWord_3768448, baseEnd_3768448] using wordTrace_append hprefix tailTrace_3768448
  have hstable : (prefixWord ++ tailWord_3768448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768448).length < 2 ^ (prefixWord ++ tailWord_3768448).sum := by decide
  have hdescent : baseEnd_3768448 < baseStart_3768448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768451 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 7]
def baseStart_3768451 : Nat := 118140960795 + 3768451 * 2 ^ 59
def prefixEnd_3768451 : Nat := 4983230072969 + 3 ^ 40 * 3768451 * 2
def baseEnd_3768451 : Nat := 1935026685916540651831715

theorem tailTrace_3768451 : CollatzResearch.WordTrace tailWord_3768451 prefixEnd_3768451 1935026685916540651831715 := by
  unfold tailWord_3768451
  simp only [CollatzResearch.WordTrace]
  refine ⟨137446699670553102036281207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91631133113702068024187471 137446699670553102036281207)
  ·
    refine ⟨206170049505829653054421811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137446699670553102036281207 206170049505829653054421811)
    ·
      refine ⟨309255074258744479581632717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206170049505829653054421811 309255074258744479581632717)
      ·
        refine ⟨115970652847029179843112269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309255074258744479581632717 115970652847029179843112269)
        ·
          refine ⟨43488994817635942441167101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115970652847029179843112269 43488994817635942441167101)
          ·
            refine ⟨16308373056613478415437663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43488994817635942441167101 16308373056613478415437663)
            ·
              refine ⟨24462559584920217623156495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16308373056613478415437663 24462559584920217623156495)
              ·
                refine ⟨36693839377380326434734743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24462559584920217623156495 36693839377380326434734743)
                ·
                  refine ⟨55040759066070489652102115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36693839377380326434734743 55040759066070489652102115)
                  ·
                    refine ⟨82561138599105734478153173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55040759066070489652102115 82561138599105734478153173)
                    ·
                      refine ⟨1935026685916540651831715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82561138599105734478153173 1935026685916540651831715)
                      ·
                        rfl

theorem cell23_3768451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_3768451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768451 prefixEnd_3768451 := by exact prefixLift 3768451
  have htrace : WordTrace (prefixWord ++ tailWord_3768451) baseStart_3768451 baseEnd_3768451 := by
    simpa [prefixWord, tailWord_3768451, baseEnd_3768451] using wordTrace_append hprefix tailTrace_3768451
  have hstable : (prefixWord ++ tailWord_3768451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768451).length < 2 ^ (prefixWord ++ tailWord_3768451).sum := by decide
  have hdescent : baseEnd_3768451 < baseStart_3768451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768456 : List Nat := [2, 1, 3, 4, 1, 3, 2, 1, 2, 2, 2]
def baseStart_3768456 : Nat := 118140960795 + 3768456 * 2 ^ 59
def prefixEnd_3768456 : Nat := 4983230072969 + 3 ^ 40 * 3768456 * 2
def baseEnd_3768456 : Nat := 1935029253319813132269193

theorem tailTrace_3768456 : CollatzResearch.WordTrace tailWord_3768456 prefixEnd_3768456 1935029253319813132269193 := by
  unfold tailWord_3768456
  simp only [CollatzResearch.WordTrace]
  refine ⟨68723441017767493945106611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91631254690356658593475481 68723441017767493945106611)
  ·
    refine ⟨103085161526651240917659917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68723441017767493945106611 103085161526651240917659917)
    ·
      refine ⟨38656935572494215344122469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103085161526651240917659917 38656935572494215344122469)
      ·
        refine ⟨7248175419842665377022963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38656935572494215344122469 7248175419842665377022963)
        ·
          refine ⟨10872263129763998065534445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7248175419842665377022963 10872263129763998065534445)
          ·
            refine ⟨4077098673661499274575417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10872263129763998065534445 4077098673661499274575417)
            ·
              refine ⟨3057824005246124455931563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4077098673661499274575417 3057824005246124455931563)
              ·
                refine ⟨4586736007869186683897345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3057824005246124455931563 4586736007869186683897345)
                ·
                  refine ⟨3440052005901890012923009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4586736007869186683897345 3440052005901890012923009)
                  ·
                    refine ⟨2580039004426417509692257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3440052005901890012923009 2580039004426417509692257)
                    ·
                      refine ⟨1935029253319813132269193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2580039004426417509692257 1935029253319813132269193)
                      ·
                        rfl

theorem cell23_3768456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_3768456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768456 prefixEnd_3768456 := by exact prefixLift 3768456
  have htrace : WordTrace (prefixWord ++ tailWord_3768456) baseStart_3768456 baseEnd_3768456 := by
    simpa [prefixWord, tailWord_3768456, baseEnd_3768456] using wordTrace_append hprefix tailTrace_3768456
  have hstable : (prefixWord ++ tailWord_3768456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768456).length < 2 ^ (prefixWord ++ tailWord_3768456).sum := by decide
  have hdescent : baseEnd_3768456 < baseStart_3768456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768491 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 4]
def baseStart_3768491 : Nat := 118140960795 + 3768491 * 2 ^ 59
def prefixEnd_3768491 : Nat := 4983230072969 + 3 ^ 40 * 3768491 * 2
def baseEnd_3768491 : Nat := 1935047225142720495331531

theorem tailTrace_3768491 : CollatzResearch.WordTrace tailWord_3768491 prefixEnd_3768491 1935047225142720495331531 := by
  unfold tailWord_3768491
  simp only [CollatzResearch.WordTrace]
  refine ⟨137448158590408188867737327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91632105726938792578491551 137448158590408188867737327)
  ·
    refine ⟨206172237885612283301605991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137448158590408188867737327 206172237885612283301605991)
    ·
      refine ⟨309258356828418424952408987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206172237885612283301605991 309258356828418424952408987)
      ·
        refine ⟨463887535242627637428613481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309258356828418424952408987 463887535242627637428613481)
        ·
          refine ⟨347915651431970728071460111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463887535242627637428613481 347915651431970728071460111)
          ·
            refine ⟨521873477147956092107190167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347915651431970728071460111 521873477147956092107190167)
            ·
              refine ⟨782810215721934138160785251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521873477147956092107190167 782810215721934138160785251)
              ·
                refine ⟨1174215323582901207241177877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782810215721934138160785251 1174215323582901207241177877)
                ·
                  refine ⟨55041343292948494089430213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1174215323582901207241177877 55041343292948494089430213)
                  ·
                    refine ⟨10320251867427842641768165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55041343292948494089430213 10320251867427842641768165)
                    ·
                      refine ⟨1935047225142720495331531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10320251867427842641768165 1935047225142720495331531)
                      ·
                        rfl

theorem cell23_3768491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 4].length) (baseStart_3768491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768491 prefixEnd_3768491 := by exact prefixLift 3768491
  have htrace : WordTrace (prefixWord ++ tailWord_3768491) baseStart_3768491 baseEnd_3768491 := by
    simpa [prefixWord, tailWord_3768491, baseEnd_3768491] using wordTrace_append hprefix tailTrace_3768491
  have hstable : (prefixWord ++ tailWord_3768491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768491).length < 2 ^ (prefixWord ++ tailWord_3768491).sum := by decide
  have hdescent : baseEnd_3768491 < baseStart_3768491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768521 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 3, 2, 6]
def baseStart_3768521 : Nat := 118140960795 + 3768521 * 2 ^ 59
def prefixEnd_3768521 : Nat := 4983230072969 + 3 ^ 40 * 3768521 * 2
def baseEnd_3768521 : Nat := 1935062629562355377956393

theorem tailTrace_3768521 : CollatzResearch.WordTrace tailWord_3768521 prefixEnd_3768521 1935062629562355377956393 := by
  unfold tailWord_3768521
  simp only [CollatzResearch.WordTrace]
  refine ⟨137449252780299503991329417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91632835186866335994219611 137449252780299503991329417)
  ·
    refine ⟨103086939585224627993497063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137449252780299503991329417 103086939585224627993497063)
    ·
      refine ⟨154630409377836941990245595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103086939585224627993497063 154630409377836941990245595)
      ·
        refine ⟨231945614066755412985368393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154630409377836941990245595 231945614066755412985368393)
        ·
          refine ⟨173959210550066559739026295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231945614066755412985368393 173959210550066559739026295)
          ·
            refine ⟨260938815825099839608539443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173959210550066559739026295 260938815825099839608539443)
            ·
              refine ⟨391408223737649759412809165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260938815825099839608539443 391408223737649759412809165)
              ·
                refine ⟨146778083901618659779803437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 391408223737649759412809165 146778083901618659779803437)
                ·
                  refine ⟨55041781463106997417426289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146778083901618659779803437 55041781463106997417426289)
                  ·
                    refine ⟨41281336097330248063069717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55041781463106997417426289 41281336097330248063069717)
                    ·
                      refine ⟨1935062629562355377956393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41281336097330248063069717 1935062629562355377956393)
                      ·
                        rfl

theorem cell23_3768521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_3768521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768521 prefixEnd_3768521 := by exact prefixLift 3768521
  have htrace : WordTrace (prefixWord ++ tailWord_3768521) baseStart_3768521 baseEnd_3768521 := by
    simpa [prefixWord, tailWord_3768521, baseEnd_3768521] using wordTrace_append hprefix tailTrace_3768521
  have hstable : (prefixWord ++ tailWord_3768521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768521).length < 2 ^ (prefixWord ++ tailWord_3768521).sum := by decide
  have hdescent : baseEnd_3768521 < baseStart_3768521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768545 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 5, 1, 3]
def baseStart_3768545 : Nat := 118140960795 + 3768545 * 2 ^ 59
def prefixEnd_3768545 : Nat := 4983230072969 + 3 ^ 40 * 3768545 * 2
def baseEnd_3768545 : Nat := 1935074953098063284056283

theorem tailTrace_3768545 : CollatzResearch.WordTrace tailWord_3768545 prefixEnd_3768545 1935074953098063284056283 := by
  unfold tailWord_3768545
  simp only [CollatzResearch.WordTrace]
  refine ⟨137450128132212556090203089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91633418754808370726802059 137450128132212556090203089)
  ·
    refine ⟨103087596099159417067652317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137450128132212556090203089 103087596099159417067652317)
    ·
      refine ⟨38657848537184781400369619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103087596099159417067652317 38657848537184781400369619)
      ·
        refine ⟨57986772805777172100554429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38657848537184781400369619 57986772805777172100554429)
        ·
          refine ⟨21745039802166439537707911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57986772805777172100554429 21745039802166439537707911)
          ·
            refine ⟨32617559703249659306561867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21745039802166439537707911 32617559703249659306561867)
            ·
              refine ⟨48926339554874488959842801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32617559703249659306561867 48926339554874488959842801)
              ·
                refine ⟨36694754666155866719882101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48926339554874488959842801 36694754666155866719882101)
                ·
                  refine ⟨3440133249952112504988947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36694754666155866719882101 3440133249952112504988947)
                  ·
                    refine ⟨5160199874928168757483421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3440133249952112504988947 5160199874928168757483421)
                    ·
                      refine ⟨1935074953098063284056283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5160199874928168757483421 1935074953098063284056283)
                      ·
                        rfl

theorem cell23_3768545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_3768545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768545 prefixEnd_3768545 := by exact prefixLift 3768545
  have htrace : WordTrace (prefixWord ++ tailWord_3768545) baseStart_3768545 baseEnd_3768545 := by
    simpa [prefixWord, tailWord_3768545, baseEnd_3768545] using wordTrace_append hprefix tailTrace_3768545
  have hstable : (prefixWord ++ tailWord_3768545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768545).length < 2 ^ (prefixWord ++ tailWord_3768545).sum := by decide
  have hdescent : baseEnd_3768545 < baseStart_3768545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768555 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 4, 3, 2]
def baseStart_3768555 : Nat := 118140960795 + 3768555 * 2 ^ 59
def prefixEnd_3768555 : Nat := 4983230072969 + 3 ^ 40 * 3768555 * 2
def baseEnd_3768555 : Nat := 1935080087904608244931237

theorem tailTrace_3768555 : CollatzResearch.WordTrace tailWord_3768555 prefixEnd_3768555 1935080087904608244931237 := by
  unfold tailWord_3768555
  simp only [CollatzResearch.WordTrace]
  refine ⟨137450492862176327798067119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91633661908117551865378079 137450492862176327798067119)
  ·
    refine ⟨206175739293264491697100679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137450492862176327798067119 206175739293264491697100679)
    ·
      refine ⟨309263608939896737545651019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206175739293264491697100679 309263608939896737545651019)
      ·
        refine ⟨463895413409845106318476529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309263608939896737545651019 463895413409845106318476529)
        ·
          refine ⟨347921560057383829738857397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463895413409845106318476529 347921560057383829738857397)
          ·
            refine ⟨32617646255379734038017881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 347921560057383829738857397 32617646255379734038017881)
            ·
              refine ⟨24463234691534800528513411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32617646255379734038017881 24463234691534800528513411)
              ·
                refine ⟨36694852037302200792770117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24463234691534800528513411 36694852037302200792770117)
                ·
                  refine ⟨6880284756994162648644397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36694852037302200792770117 6880284756994162648644397)
                  ·
                    refine ⟨2580106783872810993241649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6880284756994162648644397 2580106783872810993241649)
                    ·
                      refine ⟨1935080087904608244931237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2580106783872810993241649 1935080087904608244931237)
                      ·
                        rfl

theorem cell23_3768555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 3, 2].length) (baseStart_3768555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768555 prefixEnd_3768555 := by exact prefixLift 3768555
  have htrace : WordTrace (prefixWord ++ tailWord_3768555) baseStart_3768555 baseEnd_3768555 := by
    simpa [prefixWord, tailWord_3768555, baseEnd_3768555] using wordTrace_append hprefix tailTrace_3768555
  have hstable : (prefixWord ++ tailWord_3768555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768555).length < 2 ^ (prefixWord ++ tailWord_3768555).sum := by decide
  have hdescent : baseEnd_3768555 < baseStart_3768555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768562 : List Nat := [3, 2, 1, 3, 2, 1, 1, 3, 3, 1, 3]
def baseStart_3768562 : Nat := 118140960795 + 3768562 * 2 ^ 59
def prefixEnd_3768562 : Nat := 4983230072969 + 3 ^ 40 * 3768562 * 2
def baseEnd_3768562 : Nat := 1935083682269189717543705

theorem tailTrace_3768562 : CollatzResearch.WordTrace tailWord_3768562 prefixEnd_3768562 1935083682269189717543705 := by
  unfold tailWord_3768562
  simp only [CollatzResearch.WordTrace]
  refine ⟨34362687043287741998392985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91633832115433978662381293 34362687043287741998392985)
  ·
    refine ⟨25772015282465806498794739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34362687043287741998392985 25772015282465806498794739)
    ·
      refine ⟨38658022923698709748192109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25772015282465806498794739 38658022923698709748192109)
      ·
        refine ⟨14496758596387016155572041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38658022923698709748192109 14496758596387016155572041)
        ·
          refine ⟨10872568947290262116679031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14496758596387016155572041 10872568947290262116679031)
          ·
            refine ⟨16308853420935393175018547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10872568947290262116679031 16308853420935393175018547)
            ·
              refine ⟨24463280131403089762527821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16308853420935393175018547 24463280131403089762527821)
              ·
                refine ⟨9173730049276158660947933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24463280131403089762527821 9173730049276158660947933)
                ·
                  refine ⟨3440148768478559497855475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9173730049276158660947933 3440148768478559497855475)
                  ·
                    refine ⟨5160223152717839246783213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3440148768478559497855475 5160223152717839246783213)
                    ·
                      refine ⟨1935083682269189717543705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5160223152717839246783213 1935083682269189717543705)
                      ·
                        rfl

theorem cell23_3768562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_3768562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768562 prefixEnd_3768562 := by exact prefixLift 3768562
  have htrace : WordTrace (prefixWord ++ tailWord_3768562) baseStart_3768562 baseEnd_3768562 := by
    simpa [prefixWord, tailWord_3768562, baseEnd_3768562] using wordTrace_append hprefix tailTrace_3768562
  have hstable : (prefixWord ++ tailWord_3768562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768562).length < 2 ^ (prefixWord ++ tailWord_3768562).sum := by decide
  have hdescent : baseEnd_3768562 < baseStart_3768562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768568 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 5, 1, 4]
def baseStart_3768568 : Nat := 118140960795 + 3768568 * 2 ^ 59
def prefixEnd_3768568 : Nat := 4983230072969 + 3 ^ 40 * 3768568 * 2
def baseEnd_3768568 : Nat := 1935086763153116694068677

theorem tailTrace_3768568 : CollatzResearch.WordTrace tailWord_3768568 prefixEnd_3768568 1935086763153116694068677 := by
  unfold tailWord_3768568
  simp only [CollatzResearch.WordTrace]
  refine ⟨68725483505564615509145179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91633978007419487345526905 68725483505564615509145179)
  ·
    refine ⟨103088225258346923263717769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68725483505564615509145179 103088225258346923263717769)
    ·
      refine ⟨77316168943760192447788327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103088225258346923263717769 77316168943760192447788327)
      ·
        refine ⟨115974253415640288671682491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77316168943760192447788327 115974253415640288671682491)
        ·
          refine ⟨173961380123460433007523737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115974253415640288671682491 173961380123460433007523737)
          ·
            refine ⟨130471035092595324755642803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173961380123460433007523737 130471035092595324755642803)
            ·
              refine ⟨195706552638892987133464205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130471035092595324755642803 195706552638892987133464205)
              ·
                refine ⟨73389957239584870175049077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195706552638892987133464205 73389957239584870175049077)
                ·
                  refine ⟨6880308491211081578910851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73389957239584870175049077 6880308491211081578910851)
                  ·
                    refine ⟨10320462736816622368366277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6880308491211081578910851 10320462736816622368366277)
                    ·
                      refine ⟨1935086763153116694068677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10320462736816622368366277 1935086763153116694068677)
                      ·
                        rfl

theorem cell23_3768568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_3768568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768568 prefixEnd_3768568 := by exact prefixLift 3768568
  have htrace : WordTrace (prefixWord ++ tailWord_3768568) baseStart_3768568 baseEnd_3768568 := by
    simpa [prefixWord, tailWord_3768568, baseEnd_3768568] using wordTrace_append hprefix tailTrace_3768568
  have hstable : (prefixWord ++ tailWord_3768568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768568).length < 2 ^ (prefixWord ++ tailWord_3768568).sum := by decide
  have hdescent : baseEnd_3768568 < baseStart_3768568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768585 : List Nat := [1, 2, 1, 1, 3, 4, 1, 4, 1, 1, 4]
def baseStart_3768585 : Nat := 118140960795 + 3768585 * 2 ^ 59
def prefixEnd_3768585 : Nat := 4983230072969 + 3 ^ 40 * 3768585 * 2
def baseEnd_3768585 : Nat := 1935095492324243127556099

theorem tailTrace_3768585 : CollatzResearch.WordTrace tailWord_3768585 prefixEnd_3768585 1935095492324243127556099 := by
  unfold tailWord_3768585
  simp only [CollatzResearch.WordTrace]
  refine ⟨137451587052067642921659209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91634391368045095281106139 137451587052067642921659209)
  ·
    refine ⟨103088690289050732191244407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137451587052067642921659209 103088690289050732191244407)
    ·
      refine ⟨154633035433576098286866611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103088690289050732191244407 154633035433576098286866611)
      ·
        refine ⟨231949553150364147430299917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154633035433576098286866611 231949553150364147430299917)
        ·
          refine ⟨86981082431386555286362469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231949553150364147430299917 86981082431386555286362469)
          ·
            refine ⟨16308952955884979116192963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86981082431386555286362469 16308952955884979116192963)
            ·
              refine ⟨24463429433827468674289445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16308952955884979116192963 24463429433827468674289445)
              ·
                refine ⟨4586893018842650376429271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24463429433827468674289445 4586893018842650376429271)
                ·
                  refine ⟨6880339528263975564643907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4586893018842650376429271 6880339528263975564643907)
                  ·
                    refine ⟨10320509292395963346965861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6880339528263975564643907 10320509292395963346965861)
                    ·
                      refine ⟨1935095492324243127556099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10320509292395963346965861 1935095492324243127556099)
                      ·
                        rfl

theorem cell23_3768585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 1, 4].length) (baseStart_3768585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768585 prefixEnd_3768585 := by exact prefixLift 3768585
  have htrace : WordTrace (prefixWord ++ tailWord_3768585) baseStart_3768585 baseEnd_3768585 := by
    simpa [prefixWord, tailWord_3768585, baseEnd_3768585] using wordTrace_append hprefix tailTrace_3768585
  have hstable : (prefixWord ++ tailWord_3768585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768585).length < 2 ^ (prefixWord ++ tailWord_3768585).sum := by decide
  have hdescent : baseEnd_3768585 < baseStart_3768585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768588 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 3, 1, 5]
def baseStart_3768588 : Nat := 118140960795 + 3768588 * 2 ^ 59
def prefixEnd_3768588 : Nat := 4983230072969 + 3 ^ 40 * 3768588 * 2
def baseEnd_3768588 : Nat := 1935097032766206615818585

theorem tailTrace_3768588 : CollatzResearch.WordTrace tailWord_3768588 prefixEnd_3768588 1935097032766206615818585 := by
  unfold tailWord_3768588
  simp only [CollatzResearch.WordTrace]
  refine ⟨68725848235528387217009209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91634464314037849622678945 68725848235528387217009209)
  ·
    refine ⟨51544386176646290412756907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68725848235528387217009209 51544386176646290412756907)
    ·
      refine ⟨77316579264969435619135361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51544386176646290412756907 77316579264969435619135361)
      ·
        refine ⟨57987434448727076714351521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77316579264969435619135361 57987434448727076714351521)
        ·
          refine ⟨43490575836545307535763641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57987434448727076714351521 43490575836545307535763641)
          ·
            refine ⟨32617931877408980651822731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43490575836545307535763641 32617931877408980651822731)
            ·
              refine ⟨48926897816113470977734097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32617931877408980651822731 48926897816113470977734097)
              ·
                refine ⟨36695173362085103233300573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48926897816113470977734097 36695173362085103233300573)
                ·
                  refine ⟨13760690010781913712487715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36695173362085103233300573 13760690010781913712487715)
                  ·
                    refine ⟨20641035016172870568731573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13760690010781913712487715 20641035016172870568731573)
                    ·
                      refine ⟨1935097032766206615818585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20641035016172870568731573 1935097032766206615818585)
                      ·
                        rfl

theorem cell23_3768588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_3768588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768588 prefixEnd_3768588 := by exact prefixLift 3768588
  have htrace : WordTrace (prefixWord ++ tailWord_3768588) baseStart_3768588 baseEnd_3768588 := by
    simpa [prefixWord, tailWord_3768588, baseEnd_3768588] using wordTrace_append hprefix tailTrace_3768588
  have hstable : (prefixWord ++ tailWord_3768588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768588).length < 2 ^ (prefixWord ++ tailWord_3768588).sum := by decide
  have hdescent : baseEnd_3768588 < baseStart_3768588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768606 : List Nat := [4, 3, 2, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_3768606 : Nat := 118140960795 + 3768606 * 2 ^ 59
def prefixEnd_3768606 : Nat := 4983230072969 + 3 ^ 40 * 3768606 * 2
def baseEnd_3768606 : Nat := 1935106275417987545393503

theorem tailTrace_3768606 : CollatzResearch.WordTrace tailWord_3768606 prefixEnd_3768606 1935106275417987545393503 := by
  unfold tailWord_3768606
  simp only [CollatzResearch.WordTrace]
  refine ⟨17181544123123945438521709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91634901989994375672115781 17181544123123945438521709)
  ·
    refine ⟨6443079046171479539445641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17181544123123945438521709 6443079046171479539445641)
    ·
      refine ⟨4832309284628609654584231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6443079046171479539445641 4832309284628609654584231)
      ·
        refine ⟨7248463926942914481876347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4832309284628609654584231 7248463926942914481876347)
        ·
          refine ⟨10872695890414371722814521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7248463926942914481876347 10872695890414371722814521)
          ·
            refine ⟨8154521917810778792110891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10872695890414371722814521 8154521917810778792110891)
            ·
              refine ⟨12231782876716168188166337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8154521917810778792110891 12231782876716168188166337)
              ·
                refine ⟨9173837157537126141124753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12231782876716168188166337 9173837157537126141124753)
                ·
                  refine ⟨6880377868152844605843565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9173837157537126141124753 6880377868152844605843565)
                  ·
                    refine ⟨2580141700557316727191337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6880377868152844605843565 2580141700557316727191337)
                    ·
                      refine ⟨1935106275417987545393503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2580141700557316727191337 1935106275417987545393503)
                      ·
                        rfl

theorem cell23_3768606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_3768606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768606 prefixEnd_3768606 := by exact prefixLift 3768606
  have htrace : WordTrace (prefixWord ++ tailWord_3768606) baseStart_3768606 baseEnd_3768606 := by
    simpa [prefixWord, tailWord_3768606, baseEnd_3768606] using wordTrace_append hprefix tailTrace_3768606
  have hstable : (prefixWord ++ tailWord_3768606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768606).length < 2 ^ (prefixWord ++ tailWord_3768606).sum := by decide
  have hdescent : baseEnd_3768606 < baseStart_3768606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768608 : List Nat := [2, 1, 1, 5, 2, 1, 11]
def baseStart_3768608 : Nat := 118140960795 + 3768608 * 2 ^ 59
def prefixEnd_3768608 : Nat := 4983230072969 + 3 ^ 40 * 3768608 * 2
def baseEnd_3768608 : Nat := 23890213609620944908253

theorem tailTrace_3768608 : CollatzResearch.WordTrace tailWord_3768608 prefixEnd_3768608 23890213609620944908253 := by
  unfold tailWord_3768608
  simp only [CollatzResearch.WordTrace]
  refine ⟨68726212965492158924873239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91634950620656211899830985 68726212965492158924873239)
  ·
    refine ⟨103089319448238238387309859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68726212965492158924873239 103089319448238238387309859)
    ·
      refine ⟨154633979172357357580964789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103089319448238238387309859 154633979172357357580964789)
      ·
        refine ⟨14496935547408502273215449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154633979172357357580964789 14496935547408502273215449)
        ·
          refine ⟨10872701660556376704911587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14496935547408502273215449 10872701660556376704911587)
          ·
            refine ⟨16309052490834565057367381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10872701660556376704911587 16309052490834565057367381)
            ·
              refine ⟨23890213609620944908253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16309052490834565057367381 23890213609620944908253)
              ·
                rfl

theorem cell23_3768608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 11].length) (baseStart_3768608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768608 prefixEnd_3768608 := by exact prefixLift 3768608
  have htrace : WordTrace (prefixWord ++ tailWord_3768608) baseStart_3768608 baseEnd_3768608 := by
    simpa [prefixWord, tailWord_3768608, baseEnd_3768608] using wordTrace_append hprefix tailTrace_3768608
  have hstable : (prefixWord ++ tailWord_3768608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768608).length < 2 ^ (prefixWord ++ tailWord_3768608).sum := by decide
  have hdescent : baseEnd_3768608 < baseStart_3768608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768625 : List Nat := [1, 2, 2, 3, 4, 1, 2, 8]
def baseStart_3768625 : Nat := 118140960795 + 3768625 * 2 ^ 59
def prefixEnd_3768625 : Nat := 4983230072969 + 3 ^ 40 * 3768625 * 2
def baseEnd_3768625 : Nat := 71670964131497147076145

theorem tailTrace_3768625 : CollatzResearch.WordTrace tailWord_3768625 prefixEnd_3768625 71670964131497147076145 := by
  unfold tailWord_3768625
  simp only [CollatzResearch.WordTrace]
  refine ⟨137453045971922729753115329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91635363981281819835410219 137453045971922729753115329)
  ·
    refine ⟨103089784478942047314836497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137453045971922729753115329 103089784478942047314836497)
    ·
      refine ⟨77317338359206535486127373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103089784478942047314836497 77317338359206535486127373)
      ·
        refine ⟨28994001884702450807297765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77317338359206535486127373 28994001884702450807297765)
        ·
          refine ⟨5436375353381709526368331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28994001884702450807297765 5436375353381709526368331)
          ·
            refine ⟨8154563030072564289552497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5436375353381709526368331 8154563030072564289552497)
            ·
              refine ⟨6115922272554423217164373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8154563030072564289552497 6115922272554423217164373)
              ·
                refine ⟨71670964131497147076145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6115922272554423217164373 71670964131497147076145)
                ·
                  rfl

theorem cell23_3768625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 8].length) (baseStart_3768625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768625 prefixEnd_3768625 := by exact prefixLift 3768625
  have htrace : WordTrace (prefixWord ++ tailWord_3768625) baseStart_3768625 baseEnd_3768625 := by
    simpa [prefixWord, tailWord_3768625, baseEnd_3768625] using wordTrace_append hprefix tailTrace_3768625
  have hstable : (prefixWord ++ tailWord_3768625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768625).length < 2 ^ (prefixWord ++ tailWord_3768625).sum := by decide
  have hdescent : baseEnd_3768625 < baseStart_3768625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768648 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_3768648 : Nat := 118140960795 + 3768648 * 2 ^ 59
def prefixEnd_3768648 : Nat := 4983230072969 + 3 ^ 40 * 3768648 * 2
def baseEnd_3768648 : Nat := 1935127841605476381068309

theorem tailTrace_3768648 : CollatzResearch.WordTrace tailWord_3768648 prefixEnd_3768648 1935127841605476381068309 := by
  unfold tailWord_3768648
  simp only [CollatzResearch.WordTrace]
  refine ⟨68726942425419702340601299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91635923233892936454135065 68726942425419702340601299)
  ·
    refine ⟨103090413638129553510901949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68726942425419702340601299 103090413638129553510901949)
    ·
      refine ⟨38658905114298582566588231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103090413638129553510901949 38658905114298582566588231)
      ·
        refine ⟨57988357671447873849882347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38658905114298582566588231 57988357671447873849882347)
        ·
          refine ⟨86982536507171810774823521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57988357671447873849882347 86982536507171810774823521)
          ·
            refine ⟨65236902380378858081117641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86982536507171810774823521 65236902380378858081117641)
            ·
              refine ⟨48927676785284143560838231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65236902380378858081117641 48927676785284143560838231)
              ·
                refine ⟨73391515177926215341257347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48927676785284143560838231 73391515177926215341257347)
                ·
                  refine ⟨110087272766889323011886021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73391515177926215341257347 110087272766889323011886021)
                  ·
                    refine ⟨20641363643791748064728629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110087272766889323011886021 20641363643791748064728629)
                    ·
                      refine ⟨1935127841605476381068309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20641363643791748064728629 1935127841605476381068309)
                      ·
                        rfl

theorem cell23_3768648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_3768648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768648 prefixEnd_3768648 := by exact prefixLift 3768648
  have htrace : WordTrace (prefixWord ++ tailWord_3768648) baseStart_3768648 baseEnd_3768648 := by
    simpa [prefixWord, tailWord_3768648, baseEnd_3768648] using wordTrace_append hprefix tailTrace_3768648
  have hstable : (prefixWord ++ tailWord_3768648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768648).length < 2 ^ (prefixWord ++ tailWord_3768648).sum := by decide
  have hdescent : baseEnd_3768648 < baseStart_3768648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768685 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_3768685 : Nat := 118140960795 + 3768685 * 2 ^ 59
def prefixEnd_3768685 : Nat := 4983230072969 + 3 ^ 40 * 3768685 * 2
def baseEnd_3768685 : Nat := 645048946796564245435213

theorem tailTrace_3768685 : CollatzResearch.WordTrace tailWord_3768685 prefixEnd_3768685 645048946796564245435213 := by
  unfold tailWord_3768685
  simp only [CollatzResearch.WordTrace]
  refine ⟨137455234351705360000299509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91636822901136906666866339 137455234351705360000299509)
  ·
    refine ⟨12886428220472377500028079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137455234351705360000299509 12886428220472377500028079)
    ·
      refine ⟨19329642330708566250042119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12886428220472377500028079 19329642330708566250042119)
      ·
        refine ⟨28994463496062849375063179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19329642330708566250042119 28994463496062849375063179)
        ·
          refine ⟨43491695244094274062594769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28994463496062849375063179 43491695244094274062594769)
          ·
            refine ⟨32618771433070705546946077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43491695244094274062594769 32618771433070705546946077)
            ·
              refine ⟨12232039287401514580104779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32618771433070705546946077 12232039287401514580104779)
              ·
                refine ⟨18348058931102271870157169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12232039287401514580104779 18348058931102271870157169)
                ·
                  refine ⟨13761044198326703902617877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18348058931102271870157169 13761044198326703902617877)
                  ·
                    refine ⟨645048946796564245435213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13761044198326703902617877 645048946796564245435213)
                    ·
                      rfl

theorem cell23_3768685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_3768685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768685 prefixEnd_3768685 := by exact prefixLift 3768685
  have htrace : WordTrace (prefixWord ++ tailWord_3768685) baseStart_3768685 baseEnd_3768685 := by
    simpa [prefixWord, tailWord_3768685, baseEnd_3768685] using wordTrace_append hprefix tailTrace_3768685
  have hstable : (prefixWord ++ tailWord_3768685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768685).length < 2 ^ (prefixWord ++ tailWord_3768685).sum := by decide
  have hdescent : baseEnd_3768685 < baseStart_3768685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768743 : List Nat := [1, 1, 6, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_3768743 : Nat := 118140960795 + 3768743 * 2 ^ 59
def prefixEnd_3768743 : Nat := 4983230072969 + 3 ^ 40 * 3768743 * 2
def baseEnd_3768743 : Nat := 1935176622267653509380373

theorem tailTrace_3768743 : CollatzResearch.WordTrace tailWord_3768743 prefixEnd_3768743 1935176622267653509380373 := by
  unfold tailWord_3768743
  simp only [CollatzResearch.WordTrace]
  refine ⟨137457349785495235905910883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91638233190330157270607255 137457349785495235905910883)
  ·
    refine ⟨206186024678242853858866325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137457349785495235905910883 206186024678242853858866325)
    ·
      refine ⟨9664969906792633774634359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 206186024678242853858866325 9664969906792633774634359)
      ·
        refine ⟨14497454860188950661951539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9664969906792633774634359 14497454860188950661951539)
        ·
          refine ⟨21746182290283425992927309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14497454860188950661951539 21746182290283425992927309)
          ·
            refine ⟨8154818358856284747347741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21746182290283425992927309 8154818358856284747347741)
            ·
              refine ⟨3058056884571106780255403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8154818358856284747347741 3058056884571106780255403)
              ·
                refine ⟨4587085326856660170383105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3058056884571106780255403 4587085326856660170383105)
                ·
                  refine ⟨3440313995142495127787329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4587085326856660170383105 3440313995142495127787329)
                  ·
                    refine ⟨2580235496356871345840497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3440313995142495127787329 2580235496356871345840497)
                    ·
                      refine ⟨1935176622267653509380373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2580235496356871345840497 1935176622267653509380373)
                      ·
                        rfl

theorem cell23_3768743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_3768743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768743 prefixEnd_3768743 := by exact prefixLift 3768743
  have htrace : WordTrace (prefixWord ++ tailWord_3768743) baseStart_3768743 baseEnd_3768743 := by
    simpa [prefixWord, tailWord_3768743, baseEnd_3768743] using wordTrace_append hprefix tailTrace_3768743
  have hstable : (prefixWord ++ tailWord_3768743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768743).length < 2 ^ (prefixWord ++ tailWord_3768743).sum := by decide
  have hdescent : baseEnd_3768743 < baseStart_3768743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768839 : List Nat := [1, 1, 4, 3, 3, 1, 2, 2, 6]
def baseStart_3768839 : Nat := 118140960795 + 3768839 * 2 ^ 59
def prefixEnd_3768839 : Nat := 4983230072969 + 3 ^ 40 * 3768839 * 2
def baseEnd_3768839 : Nat := 215025101823387237086659

theorem tailTrace_3768839 : CollatzResearch.WordTrace tailWord_3768839 prefixEnd_3768839 215025101823387237086659 := by
  unfold tailWord_3768839
  simp only [CollatzResearch.WordTrace]
  refine ⟨137460851193147444301405571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91640567462098296200937047 137460851193147444301405571)
  ·
    refine ⟨206191276789721166452108357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137460851193147444301405571 206191276789721166452108357)
    ·
      refine ⟨38660864398072718709770317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206191276789721166452108357 38660864398072718709770317)
      ·
        refine ⟨14497824149277269516163869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38660864398072718709770317 14497824149277269516163869)
        ·
          refine ⟨5436684055978976068561451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14497824149277269516163869 5436684055978976068561451)
          ·
            refine ⟨8155026083968464102842177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5436684055978976068561451 8155026083968464102842177)
            ·
              refine ⟨6116269562976348077131633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8155026083968464102842177 6116269562976348077131633)
              ·
                refine ⟨4587202172232261057848725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6116269562976348077131633 4587202172232261057848725)
                ·
                  refine ⟨215025101823387237086659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4587202172232261057848725 215025101823387237086659)
                  ·
                    rfl

theorem cell23_3768839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 6].length) (baseStart_3768839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768839 prefixEnd_3768839 := by exact prefixLift 3768839
  have htrace : WordTrace (prefixWord ++ tailWord_3768839) baseStart_3768839 baseEnd_3768839 := by
    simpa [prefixWord, tailWord_3768839, baseEnd_3768839] using wordTrace_append hprefix tailTrace_3768839
  have hstable : (prefixWord ++ tailWord_3768839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768839).length < 2 ^ (prefixWord ++ tailWord_3768839).sum := by decide
  have hdescent : baseEnd_3768839 < baseStart_3768839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768843 : List Nat := [1, 1, 1, 1, 7, 3, 2, 2, 1, 4]
def baseStart_3768843 : Nat := 118140960795 + 3768843 * 2 ^ 59
def prefixEnd_3768843 : Nat := 4983230072969 + 3 ^ 40 * 3768843 * 2
def baseEnd_3768843 : Nat := 645075990111034372709971

theorem tailTrace_3768843 : CollatzResearch.WordTrace tailWord_3768843 prefixEnd_3768843 645075990111034372709971 := by
  unfold tailWord_3768843
  simp only [CollatzResearch.WordTrace]
  refine ⟨137460997085132952984551183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91640664723421968656367455 137460997085132952984551183)
  ·
    refine ⟨206191495627699429476826775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137460997085132952984551183 206191495627699429476826775)
    ·
      refine ⟨309287243441549144215240163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206191495627699429476826775 309287243441549144215240163)
      ·
        refine ⟨463930865162323716322860245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309287243441549144215240163 463930865162323716322860245)
        ·
          refine ⟨10873379652241962101317037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 463930865162323716322860245 10873379652241962101317037)
          ·
            refine ⟨4077517369590735787993889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10873379652241962101317037 4077517369590735787993889)
            ·
              refine ⟨3058138027193051840995417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4077517369590735787993889 3058138027193051840995417)
              ·
                refine ⟨2293603520394788880746563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3058138027193051840995417 2293603520394788880746563)
                ·
                  refine ⟨3440405280592183321119845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293603520394788880746563 3440405280592183321119845)
                  ·
                    refine ⟨645075990111034372709971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3440405280592183321119845 645075990111034372709971)
                    ·
                      rfl

theorem cell23_3768843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 1, 4].length) (baseStart_3768843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768843 prefixEnd_3768843 := by exact prefixLift 3768843
  have htrace : WordTrace (prefixWord ++ tailWord_3768843) baseStart_3768843 baseEnd_3768843 := by
    simpa [prefixWord, tailWord_3768843, baseEnd_3768843] using wordTrace_append hprefix tailTrace_3768843
  have hstable : (prefixWord ++ tailWord_3768843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768843).length < 2 ^ (prefixWord ++ tailWord_3768843).sum := by decide
  have hdescent : baseEnd_3768843 < baseStart_3768843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768877 : List Nat := [1, 5, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_3768877 : Nat := 118140960795 + 3768877 * 2 ^ 59
def prefixEnd_3768877 : Nat := 4983230072969 + 3 ^ 40 * 3768877 * 2
def baseEnd_3768877 : Nat := 645081809558451995034919

theorem tailTrace_3768877 : CollatzResearch.WordTrace tailWord_3768877 prefixEnd_3768877 645081809558451995034919 := by
  unfold tailWord_3768877
  simp only [CollatzResearch.WordTrace]
  refine ⟨137462237167009776791288885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91641491444673184527525923 137462237167009776791288885)
  ·
    refine ⟨12887084734407166574183333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137462237167009776791288885 12887084734407166574183333)
    ·
      refine ⟨2416328387701343732659375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12887084734407166574183333 2416328387701343732659375)
      ·
        refine ⟨3624492581552015598989063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2416328387701343732659375 3624492581552015598989063)
        ·
          refine ⟨5436738872328023398483595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3624492581552015598989063 5436738872328023398483595)
          ·
            refine ⟨8155108308492035097725393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5436738872328023398483595 8155108308492035097725393)
            ·
              refine ⟨6116331231369026323294045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8155108308492035097725393 6116331231369026323294045)
              ·
                refine ⟨2293624211763384871235267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6116331231369026323294045 2293624211763384871235267)
                ·
                  refine ⟨3440436317645077306852901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293624211763384871235267 3440436317645077306852901)
                  ·
                    refine ⟨645081809558451995034919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3440436317645077306852901 645081809558451995034919)
                    ·
                      rfl

theorem cell23_3768877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_3768877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768877 prefixEnd_3768877 := by exact prefixLift 3768877
  have htrace : WordTrace (prefixWord ++ tailWord_3768877) baseStart_3768877 baseEnd_3768877 := by
    simpa [prefixWord, tailWord_3768877, baseEnd_3768877] using wordTrace_append hprefix tailTrace_3768877
  have hstable : (prefixWord ++ tailWord_3768877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768877).length < 2 ^ (prefixWord ++ tailWord_3768877).sum := by decide
  have hdescent : baseEnd_3768877 < baseStart_3768877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768882 : List Nat := [3, 2, 1, 1, 2, 1, 4, 2, 1, 6]
def baseStart_3768882 : Nat := 118140960795 + 3768882 * 2 ^ 59
def prefixEnd_3768882 : Nat := 4983230072969 + 3 ^ 40 * 3768882 * 2
def baseEnd_3768882 : Nat := 645082665359542821847411

theorem tailTrace_3768882 : CollatzResearch.WordTrace tailWord_3768882 prefixEnd_3768882 645082665359542821847411 := by
  unfold tailWord_3768882
  simp only [CollatzResearch.WordTrace]
  refine ⟨34365604882997915661305225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91641613021327775096813933 34365604882997915661305225)
  ·
    refine ⟨25774203662248436745978919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34365604882997915661305225 25774203662248436745978919)
    ·
      refine ⟨38661305493372655118968379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25774203662248436745978919 38661305493372655118968379)
      ·
        refine ⟨57991958240058982678452569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38661305493372655118968379 57991958240058982678452569)
        ·
          refine ⟨43493968680044237008839427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57991958240058982678452569 43493968680044237008839427)
          ·
            refine ⟨65240953020066355513259141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43493968680044237008839427 65240953020066355513259141)
            ·
              refine ⟨12232678691262441658736089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65240953020066355513259141 12232678691262441658736089)
              ·
                refine ⟨9174509018446831244052067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12232678691262441658736089 9174509018446831244052067)
                ·
                  refine ⟨13761763527670246866078101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9174509018446831244052067 13761763527670246866078101)
                  ·
                    refine ⟨645082665359542821847411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13761763527670246866078101 645082665359542821847411)
                    ·
                      rfl

theorem cell23_3768882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_3768882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768882 prefixEnd_3768882 := by exact prefixLift 3768882
  have htrace : WordTrace (prefixWord ++ tailWord_3768882) baseStart_3768882 baseEnd_3768882 := by
    simpa [prefixWord, tailWord_3768882, baseEnd_3768882] using wordTrace_append hprefix tailTrace_3768882
  have hstable : (prefixWord ++ tailWord_3768882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768882).length < 2 ^ (prefixWord ++ tailWord_3768882).sum := by decide
  have hdescent : baseEnd_3768882 < baseStart_3768882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768886 : List Nat := [5, 1, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_3768886 : Nat := 118140960795 + 3768886 * 2 ^ 59
def prefixEnd_3768886 : Nat := 4983230072969 + 3 ^ 40 * 3768886 * 2
def baseEnd_3768886 : Nat := 645083350000415483297405

theorem tailTrace_3768886 : CollatzResearch.WordTrace tailWord_3768886 prefixEnd_3768886 645083350000415483297405 := by
  unfold tailWord_3768886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8591410338998573208022907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91641710282651447552244341 8591410338998573208022907)
  ·
    refine ⟨12887115508497859812034361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8591410338998573208022907 12887115508497859812034361)
    ·
      refine ⟨9665336631373394859025771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12887115508497859812034361 9665336631373394859025771)
      ·
        refine ⟨14498004947060092288538657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9665336631373394859025771 14498004947060092288538657)
        ·
          refine ⟨10873503710295069216403993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14498004947060092288538657 10873503710295069216403993)
          ·
            refine ⟨8155127782721301912302995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10873503710295069216403993 8155127782721301912302995)
            ·
              refine ⟨12232691674081952868454493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8155127782721301912302995 12232691674081952868454493)
              ·
                refine ⟨4587259377780732325670435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12232691674081952868454493 4587259377780732325670435)
                ·
                  refine ⟨6880889066671098488505653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4587259377780732325670435 6880889066671098488505653)
                  ·
                    refine ⟨645083350000415483297405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6880889066671098488505653 645083350000415483297405)
                    ·
                      rfl

theorem cell23_3768886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_3768886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768886 prefixEnd_3768886 := by exact prefixLift 3768886
  have htrace : WordTrace (prefixWord ++ tailWord_3768886) baseStart_3768886 baseEnd_3768886 := by
    simpa [prefixWord, tailWord_3768886, baseEnd_3768886] using wordTrace_append hprefix tailTrace_3768886
  have hstable : (prefixWord ++ tailWord_3768886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768886).length < 2 ^ (prefixWord ++ tailWord_3768886).sum := by decide
  have hdescent : baseEnd_3768886 < baseStart_3768886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768889 : List Nat := [1, 2, 1, 5, 1, 1, 3, 3, 1, 1, 4]
def baseStart_3768889 : Nat := 118140960795 + 3768889 * 2 ^ 59
def prefixEnd_3768889 : Nat := 4983230072969 + 3 ^ 40 * 3768889 * 2
def baseEnd_3768889 : Nat := 1935251590443209938154701

theorem tailTrace_3768889 : CollatzResearch.WordTrace tailWord_3768889 prefixEnd_3768889 1935251590443209938154701 := by
  unfold tailWord_3768889
  simp only [CollatzResearch.WordTrace]
  refine ⟨137462674842966302840725721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91641783228644201893817147 137462674842966302840725721)
  ·
    refine ⟨103097006132224727130544291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137462674842966302840725721 103097006132224727130544291)
    ·
      refine ⟨154645509198337090695816437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103097006132224727130544291 154645509198337090695816437)
      ·
        refine ⟨14498016487344102252732791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154645509198337090695816437 14498016487344102252732791)
        ·
          refine ⟨21747024731016153379099187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14498016487344102252732791 21747024731016153379099187)
          ·
            refine ⟨32620537096524230068648781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21747024731016153379099187 32620537096524230068648781)
            ·
              refine ⟨12232701411196586275743293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32620537096524230068648781 12232701411196586275743293)
              ·
                refine ⟨4587263029198719853403735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12232701411196586275743293 4587263029198719853403735)
                ·
                  refine ⟨6880894543798079780105603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4587263029198719853403735 6880894543798079780105603)
                  ·
                    refine ⟨10321341815697119670158405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6880894543798079780105603 10321341815697119670158405)
                    ·
                      refine ⟨1935251590443209938154701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10321341815697119670158405 1935251590443209938154701)
                      ·
                        rfl

theorem cell23_3768889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_3768889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768889 prefixEnd_3768889 := by exact prefixLift 3768889
  have htrace : WordTrace (prefixWord ++ tailWord_3768889) baseStart_3768889 baseEnd_3768889 := by
    simpa [prefixWord, tailWord_3768889, baseEnd_3768889] using wordTrace_append hprefix tailTrace_3768889
  have hstable : (prefixWord ++ tailWord_3768889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768889).length < 2 ^ (prefixWord ++ tailWord_3768889).sum := by decide
  have hdescent : baseEnd_3768889 < baseStart_3768889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768895 : List Nat := [1, 1, 2, 2, 3, 2, 12]
def baseStart_3768895 : Nat := 118140960795 + 3768895 * 2 ^ 59
def prefixEnd_3768895 : Nat := 4983230072969 + 3 ^ 40 * 3768895 * 2
def baseEnd_3768895 : Nat := 23892032979347369317033

theorem tailTrace_3768895 : CollatzResearch.WordTrace tailWord_3768895 prefixEnd_3768895 23892032979347369317033 := by
  unfold tailWord_3768895
  simp only [CollatzResearch.WordTrace]
  refine ⟨137462893680944565865444139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91641929120629710576962759 137462893680944565865444139)
  ·
    refine ⟨206194340521416848798166209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137462893680944565865444139 206194340521416848798166209)
    ·
      refine ⟨154645755391062636598624657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206194340521416848798166209 154645755391062636598624657)
      ·
        refine ⟨115984316543296977448968493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154645755391062636598624657 115984316543296977448968493)
        ·
          refine ⟨43494118703736366543363185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115984316543296977448968493 43494118703736366543363185)
          ·
            refine ⟨32620589027802274907522389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43494118703736366543363185 32620589027802274907522389)
            ·
              refine ⟨23892032979347369317033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 32620589027802274907522389 23892032979347369317033)
              ·
                rfl

theorem cell23_3768895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 12].length) (baseStart_3768895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768895 prefixEnd_3768895 := by exact prefixLift 3768895
  have htrace : WordTrace (prefixWord ++ tailWord_3768895) baseStart_3768895 baseEnd_3768895 := by
    simpa [prefixWord, tailWord_3768895, baseEnd_3768895] using wordTrace_append hprefix tailTrace_3768895
  have hstable : (prefixWord ++ tailWord_3768895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768895).length < 2 ^ (prefixWord ++ tailWord_3768895).sum := by decide
  have hdescent : baseEnd_3768895 < baseStart_3768895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768905 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 7]
def baseStart_3768905 : Nat := 118140960795 + 3768905 * 2 ^ 59
def prefixEnd_3768905 : Nat := 4983230072969 + 3 ^ 40 * 3768905 * 2
def baseEnd_3768905 : Nat := 1935259806133681875554627

theorem tailTrace_3768905 : CollatzResearch.WordTrace tailWord_3768905 prefixEnd_3768905 1935259806133681875554627 := by
  unfold tailWord_3768905
  simp only [CollatzResearch.WordTrace]
  refine ⟨137463258410908337573308169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91642172273938891715538779 137463258410908337573308169)
  ·
    refine ⟨103097443808181253179981127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137463258410908337573308169 103097443808181253179981127)
    ·
      refine ⟨154646165712271879769971691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103097443808181253179981127 154646165712271879769971691)
      ·
        refine ⟨231969248568407819654957537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154646165712271879769971691 231969248568407819654957537)
        ·
          refine ⟨173976936426305864741218153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231969248568407819654957537 173976936426305864741218153)
          ·
            refine ⟨130482702319729398555913615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173976936426305864741218153 130482702319729398555913615)
            ·
              refine ⟨195724053479594097833870423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130482702319729398555913615 195724053479594097833870423)
              ·
                refine ⟨293586080219391146750805635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195724053479594097833870423 293586080219391146750805635)
                ·
                  refine ⟨440379120329086720126208453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293586080219391146750805635 440379120329086720126208453)
                  ·
                    refine ⟨82571085061703760023664085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 440379120329086720126208453 82571085061703760023664085)
                    ·
                      refine ⟨1935259806133681875554627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82571085061703760023664085 1935259806133681875554627)
                      ·
                        rfl

theorem cell23_3768905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_3768905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768905 prefixEnd_3768905 := by exact prefixLift 3768905
  have htrace : WordTrace (prefixWord ++ tailWord_3768905) baseStart_3768905 baseEnd_3768905 := by
    simpa [prefixWord, tailWord_3768905, baseEnd_3768905] using wordTrace_append hprefix tailTrace_3768905
  have hstable : (prefixWord ++ tailWord_3768905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768905).length < 2 ^ (prefixWord ++ tailWord_3768905).sum := by decide
  have hdescent : baseEnd_3768905 < baseStart_3768905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768906 : List Nat := [3, 1, 2, 1, 1, 4, 1, 3, 3, 2, 2]
def baseStart_3768906 : Nat := 118140960795 + 3768906 * 2 ^ 59
def prefixEnd_3768906 : Nat := 4983230072969 + 3 ^ 40 * 3768906 * 2
def baseEnd_3768906 : Nat := 1935260319614336371642123

theorem tailTrace_3768906 : CollatzResearch.WordTrace tailWord_3768906 prefixEnd_3768906 1935260319614336371642123 := by
  unfold tailWord_3768906
  simp only [CollatzResearch.WordTrace]
  refine ⟨34365823720976178686023643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91642196589269809829396381 34365823720976178686023643)
  ·
    refine ⟨51548735581464268029035465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34365823720976178686023643 51548735581464268029035465)
    ·
      refine ⟨38661551686098201021776599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51548735581464268029035465 38661551686098201021776599)
      ·
        refine ⟨57992327529147301532664899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38661551686098201021776599 57992327529147301532664899)
        ·
          refine ⟨86988491293720952298997349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57992327529147301532664899 86988491293720952298997349)
          ·
            refine ⟨16310342117572678556062003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86988491293720952298997349 16310342117572678556062003)
            ·
              refine ⟨24465513176359017834093005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16310342117572678556062003 24465513176359017834093005)
              ·
                refine ⟨9174567441134631687784877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24465513176359017834093005 9174567441134631687784877)
                ·
                  refine ⟨3440462790425486882919329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9174567441134631687784877 3440462790425486882919329)
                  ·
                    refine ⟨2580347092819115162189497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3440462790425486882919329 2580347092819115162189497)
                    ·
                      refine ⟨1935260319614336371642123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2580347092819115162189497 1935260319614336371642123)
                      ·
                        rfl

theorem cell23_3768906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_3768906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768906 prefixEnd_3768906 := by exact prefixLift 3768906
  have htrace : WordTrace (prefixWord ++ tailWord_3768906) baseStart_3768906 baseEnd_3768906 := by
    simpa [prefixWord, tailWord_3768906, baseEnd_3768906] using wordTrace_append hprefix tailTrace_3768906
  have hstable : (prefixWord ++ tailWord_3768906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768906).length < 2 ^ (prefixWord ++ tailWord_3768906).sum := by decide
  have hdescent : baseEnd_3768906 < baseStart_3768906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768909 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_3768909 : Nat := 118140960795 + 3768909 * 2 ^ 59
def prefixEnd_3768909 : Nat := 4983230072969 + 3 ^ 40 * 3768909 * 2
def baseEnd_3768909 : Nat := 1935261860056299859904609

theorem tailTrace_3768909 : CollatzResearch.WordTrace tailWord_3768909 prefixEnd_3768909 1935261860056299859904609 := by
  unfold tailWord_3768909
  simp only [CollatzResearch.WordTrace]
  refine ⟨137463404302893846256453781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91642269535262564170969187 137463404302893846256453781)
  ·
    refine ⟨6443597076698149043271271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 137463404302893846256453781 6443597076698149043271271)
    ·
      refine ⟨9665395615047223564906907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6443597076698149043271271 9665395615047223564906907)
      ·
        refine ⟨14498093422570835347360361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9665395615047223564906907 14498093422570835347360361)
        ·
          refine ⟨10873570066928126510520271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14498093422570835347360361 10873570066928126510520271)
          ·
            refine ⟨16310355100392189765780407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10873570066928126510520271 16310355100392189765780407)
            ·
              refine ⟨24465532650588284648670611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16310355100392189765780407 24465532650588284648670611)
              ·
                refine ⟨36698298975882426973005917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24465532650588284648670611 36698298975882426973005917)
                ·
                  refine ⟨13761862115955910114877219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36698298975882426973005917 13761862115955910114877219)
                  ·
                    refine ⟨20642793173933865172315829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13761862115955910114877219 20642793173933865172315829)
                    ·
                      refine ⟨1935261860056299859904609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20642793173933865172315829 1935261860056299859904609)
                      ·
                        rfl

theorem cell23_3768909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_3768909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768909 prefixEnd_3768909 := by exact prefixLift 3768909
  have htrace : WordTrace (prefixWord ++ tailWord_3768909) baseStart_3768909 baseEnd_3768909 := by
    simpa [prefixWord, tailWord_3768909, baseEnd_3768909] using wordTrace_append hprefix tailTrace_3768909
  have hstable : (prefixWord ++ tailWord_3768909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768909).length < 2 ^ (prefixWord ++ tailWord_3768909).sum := by decide
  have hdescent : baseEnd_3768909 < baseStart_3768909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768929 : List Nat := [1, 2, 3, 1, 1, 6, 2, 7]
def baseStart_3768929 : Nat := 118140960795 + 3768929 * 2 ^ 59
def prefixEnd_3768929 : Nat := 4983230072969 + 3 ^ 40 * 3768929 * 2
def baseEnd_3768929 : Nat := 71676745543310732653871

theorem tailTrace_3768929 : CollatzResearch.WordTrace tailWord_3768929 prefixEnd_3768929 71676745543310732653871 := by
  unfold tailWord_3768929
  simp only [CollatzResearch.WordTrace]
  refine ⟨137464133762821389672181841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91642755841880926448121227 137464133762821389672181841)
  ·
    refine ⟨103098100322116042254136381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137464133762821389672181841 103098100322116042254136381)
    ·
      refine ⟨38661787620793515845301143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103098100322116042254136381 38661787620793515845301143)
      ·
        refine ⟨57992681431190273767951715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38661787620793515845301143 57992681431190273767951715)
        ·
          refine ⟨86989022146785410651927573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57992681431190273767951715 86989022146785410651927573)
          ·
            refine ⟨4077610413130566124309105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86989022146785410651927573 4077610413130566124309105)
            ·
              refine ⟨3058207809847924593231829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4077610413130566124309105 3058207809847924593231829)
              ·
                refine ⟨71676745543310732653871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3058207809847924593231829 71676745543310732653871)
                ·
                  rfl

theorem cell23_3768929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 7].length) (baseStart_3768929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768929 prefixEnd_3768929 := by exact prefixLift 3768929
  have htrace : WordTrace (prefixWord ++ tailWord_3768929) baseStart_3768929 baseEnd_3768929 := by
    simpa [prefixWord, tailWord_3768929, baseEnd_3768929] using wordTrace_append hprefix tailTrace_3768929
  have hstable : (prefixWord ++ tailWord_3768929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768929).length < 2 ^ (prefixWord ++ tailWord_3768929).sum := by decide
  have hdescent : baseEnd_3768929 < baseStart_3768929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768957 : List Nat := [1, 4, 1, 1, 5, 1, 3, 2, 1, 2, 2]
def baseStart_3768957 : Nat := 118140960795 + 3768957 * 2 ^ 59
def prefixEnd_3768957 : Nat := 4983230072969 + 3 ^ 40 * 3768957 * 2
def baseEnd_3768957 : Nat := 1935286507127715672104389

theorem tailTrace_3768957 : CollatzResearch.WordTrace tailWord_3768957 prefixEnd_3768957 1935286507127715672104389 := by
  unfold tailWord_3768957
  simp only [CollatzResearch.WordTrace]
  refine ⟨137465155006719950454201125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91643436671146633636134083 137465155006719950454201125)
  ·
    refine ⟨25774716563759990710162711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137465155006719950454201125 25774716563759990710162711)
    ·
      refine ⟨38662074845639986065244067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25774716563759990710162711 38662074845639986065244067)
      ·
        refine ⟨57993112268459979097866101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38662074845639986065244067 57993112268459979097866101)
        ·
          refine ⟨5436854275168123040424947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57993112268459979097866101 5436854275168123040424947)
          ·
            refine ⟨8155281412752184560637421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5436854275168123040424947 8155281412752184560637421)
            ·
              refine ⟨3058230529782069210239033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8155281412752184560637421 3058230529782069210239033)
              ·
                refine ⟨2293672897336551907679275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3058230529782069210239033 2293672897336551907679275)
                ·
                  refine ⟨3440509346004827861518913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293672897336551907679275 3440509346004827861518913)
                  ·
                    refine ⟨2580382009503620896139185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3440509346004827861518913 2580382009503620896139185)
                    ·
                      refine ⟨1935286507127715672104389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2580382009503620896139185 1935286507127715672104389)
                      ·
                        rfl

theorem cell23_3768957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_3768957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768957 prefixEnd_3768957 := by exact prefixLift 3768957
  have htrace : WordTrace (prefixWord ++ tailWord_3768957) baseStart_3768957 baseEnd_3768957 := by
    simpa [prefixWord, tailWord_3768957, baseEnd_3768957] using wordTrace_append hprefix tailTrace_3768957
  have hstable : (prefixWord ++ tailWord_3768957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768957).length < 2 ^ (prefixWord ++ tailWord_3768957).sum := by decide
  have hdescent : baseEnd_3768957 < baseStart_3768957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768996 : List Nat := [2, 3, 1, 2, 2, 1, 3, 2, 1, 4, 2]
def baseStart_3768996 : Nat := 118140960795 + 3768996 * 2 ^ 59
def prefixEnd_3768996 : Nat := 4983230072969 + 3 ^ 40 * 3768996 * 2
def baseEnd_3768996 : Nat := 1935306532873241019516709

theorem tailTrace_3768996 : CollatzResearch.WordTrace tailWord_3768996 prefixEnd_3768996 1935306532873241019516709 := by
  unfold tailWord_3768996
  simp only [CollatzResearch.WordTrace]
  refine ⟨68733288726789330057435421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91644384969052440076580561 68733288726789330057435421)
  ·
    refine ⟨25774983272545998771538283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68733288726789330057435421 25774983272545998771538283)
    ·
      refine ⟨38662474908818998157307425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25774983272545998771538283 38662474908818998157307425)
      ·
        refine ⟨28996856181614248617980569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38662474908818998157307425 28996856181614248617980569)
        ·
          refine ⟨21747642136210686463485427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28996856181614248617980569 21747642136210686463485427)
          ·
            refine ⟨32621463204316029695228141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21747642136210686463485427 32621463204316029695228141)
            ·
              refine ⟨12233048701618511135710553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32621463204316029695228141 12233048701618511135710553)
              ·
                refine ⟨9174786526213883351782915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12233048701618511135710553 9174786526213883351782915)
                ·
                  refine ⟨13762179789320825027674373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9174786526213883351782915 13762179789320825027674373)
                  ·
                    refine ⟨2580408710497654692688945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13762179789320825027674373 2580408710497654692688945)
                    ·
                      refine ⟨1935306532873241019516709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2580408710497654692688945 1935306532873241019516709)
                      ·
                        rfl

theorem cell23_3768996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_3768996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3768996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3768996 prefixEnd_3768996 := by exact prefixLift 3768996
  have htrace : WordTrace (prefixWord ++ tailWord_3768996) baseStart_3768996 baseEnd_3768996 := by
    simpa [prefixWord, tailWord_3768996, baseEnd_3768996] using wordTrace_append hprefix tailTrace_3768996
  have hstable : (prefixWord ++ tailWord_3768996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768996).length < 2 ^ (prefixWord ++ tailWord_3768996).sum := by decide
  have hdescent : baseEnd_3768996 < baseStart_3768996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769086 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_3769086 : Nat := 118140960795 + 3769086 * 2 ^ 59
def prefixEnd_3769086 : Nat := 4983230072969 + 3 ^ 40 * 3769086 * 2
def baseEnd_3769086 : Nat := 1935352746132145667391295

theorem tailTrace_3769086 : CollatzResearch.WordTrace tailWord_3769086 prefixEnd_3769086 1935352746132145667391295 := by
  unfold tailWord_3769086
  simp only [CollatzResearch.WordTrace]
  refine ⟨17183732502906575685705889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91646573348835070323764741 17183732502906575685705889)
  ·
    refine ⟨12887799377179931764279417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17183732502906575685705889 12887799377179931764279417)
    ·
      refine ⟨9665849532884948823209563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12887799377179931764279417 9665849532884948823209563)
      ·
        refine ⟨14498774299327423234814345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9665849532884948823209563 14498774299327423234814345)
        ·
          refine ⟨10874080724495567426110759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14498774299327423234814345 10874080724495567426110759)
          ·
            refine ⟨16311121086743351139166139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10874080724495567426110759 16311121086743351139166139)
            ·
              refine ⟨24466681630115026708749209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16311121086743351139166139 24466681630115026708749209)
              ·
                refine ⟨18350011222586270031561907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24466681630115026708749209 18350011222586270031561907)
                ·
                  refine ⟨27525016833879405047342861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18350011222586270031561907 27525016833879405047342861)
                  ·
                    refine ⟨10321881312704776892753573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27525016833879405047342861 10321881312704776892753573)
                    ·
                      refine ⟨1935352746132145667391295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10321881312704776892753573 1935352746132145667391295)
                      ·
                        rfl

theorem cell23_3769086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_3769086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769086 prefixEnd_3769086 := by exact prefixLift 3769086
  have htrace : WordTrace (prefixWord ++ tailWord_3769086) baseStart_3769086 baseEnd_3769086 := by
    simpa [prefixWord, tailWord_3769086, baseEnd_3769086] using wordTrace_append hprefix tailTrace_3769086
  have hstable : (prefixWord ++ tailWord_3769086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769086).length < 2 ^ (prefixWord ++ tailWord_3769086).sum := by decide
  have hdescent : baseEnd_3769086 < baseStart_3769086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769096 : List Nat := [2, 1, 3, 2, 2, 2, 2, 2, 3, 4]
def baseStart_3769096 : Nat := 118140960795 + 3769096 * 2 ^ 59
def prefixEnd_3769096 : Nat := 4983230072969 + 3 ^ 40 * 3769096 * 2
def baseEnd_3769096 : Nat := 645119293646230209422083

theorem tailTrace_3769096 : CollatzResearch.WordTrace tailWord_3769096 prefixEnd_3769096 645119293646230209422083 := by
  unfold tailWord_3769096
  simp only [CollatzResearch.WordTrace]
  refine ⟨68735112376608188596755571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91646816502144251462340761 68735112376608188596755571)
  ·
    refine ⟨103102668564912282895133357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68735112376608188596755571 103102668564912282895133357)
    ·
      refine ⟨38663500711842106085675009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103102668564912282895133357 38663500711842106085675009)
      ·
        refine ⟨28997625533881579564256257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38663500711842106085675009 28997625533881579564256257)
        ·
          refine ⟨21748219150411184673192193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28997625533881579564256257 21748219150411184673192193)
          ·
            refine ⟨16311164362808388504894145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21748219150411184673192193 16311164362808388504894145)
            ·
              refine ⟨12233373272106291378670609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16311164362808388504894145 12233373272106291378670609)
              ·
                refine ⟨9175029954079718534002957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12233373272106291378670609 9175029954079718534002957)
                ·
                  refine ⟨3440636232779894450251109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9175029954079718534002957 3440636232779894450251109)
                  ·
                    refine ⟨645119293646230209422083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3440636232779894450251109 645119293646230209422083)
                    ·
                      rfl

theorem cell23_3769096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_3769096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769096 prefixEnd_3769096 := by exact prefixLift 3769096
  have htrace : WordTrace (prefixWord ++ tailWord_3769096) baseStart_3769096 baseEnd_3769096 := by
    simpa [prefixWord, tailWord_3769096, baseEnd_3769096] using wordTrace_append hprefix tailTrace_3769096
  have hstable : (prefixWord ++ tailWord_3769096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769096).length < 2 ^ (prefixWord ++ tailWord_3769096).sum := by decide
  have hdescent : baseEnd_3769096 < baseStart_3769096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769170 : List Nat := [3, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3]
def baseStart_3769170 : Nat := 118140960795 + 3769170 * 2 ^ 59
def prefixEnd_3769170 : Nat := 4983230072969 + 3 ^ 40 * 3769170 * 2
def baseEnd_3769170 : Nat := 1935395878507123338740909

theorem tailTrace_3769170 : CollatzResearch.WordTrace tailWord_3769170 prefixEnd_3769170 1935395878507123338740909 := by
  unfold tailWord_3769170
  simp only [CollatzResearch.WordTrace]
  refine ⟨34368230938737071957926241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91648615836632191887803309 34368230938737071957926241)
  ·
    refine ⟨25776173204052803968444681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34368230938737071957926241 25776173204052803968444681)
    ·
      refine ⟨19332129903039602976333511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25776173204052803968444681 19332129903039602976333511)
      ·
        refine ⟨28998194854559404464500267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19332129903039602976333511 28998194854559404464500267)
        ·
          refine ⟨43497292281839106696750401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28998194854559404464500267 43497292281839106696750401)
          ·
            refine ⟨32622969211379330022562801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43497292281839106696750401 32622969211379330022562801)
            ·
              refine ⟨24467226908534497516922101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32622969211379330022562801 24467226908534497516922101)
              ·
                refine ⟨2293802522675109142211447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24467226908534497516922101 2293802522675109142211447)
                ·
                  refine ⟨3440703784012663713317171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293802522675109142211447 3440703784012663713317171)
                  ·
                    refine ⟨5161055676018995569975757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3440703784012663713317171 5161055676018995569975757)
                    ·
                      refine ⟨1935395878507123338740909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5161055676018995569975757 1935395878507123338740909)
                      ·
                        rfl

theorem cell23_3769170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_3769170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769170 prefixEnd_3769170 := by exact prefixLift 3769170
  have htrace : WordTrace (prefixWord ++ tailWord_3769170) baseStart_3769170 baseEnd_3769170 := by
    simpa [prefixWord, tailWord_3769170, baseEnd_3769170] using wordTrace_append hprefix tailTrace_3769170
  have hstable : (prefixWord ++ tailWord_3769170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769170).length < 2 ^ (prefixWord ++ tailWord_3769170).sum := by decide
  have hdescent : baseEnd_3769170 < baseStart_3769170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769173 : List Nat := [1, 3, 2, 2, 2, 1, 5, 1, 1, 5]
def baseStart_3769173 : Nat := 118140960795 + 3769173 * 2 ^ 59
def prefixEnd_3769173 : Nat := 4983230072969 + 3 ^ 40 * 3769173 * 2
def baseEnd_3769173 : Nat := 645132472983028942334465

theorem tailTrace_3769173 : CollatzResearch.WordTrace tailWord_3769173 prefixEnd_3769173 645132472983028942334465 := by
  unfold tailWord_3769173
  simp only [CollatzResearch.WordTrace]
  refine ⟨137473033173937419344064173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91648688782624946229376115 137473033173937419344064173)
  ·
    refine ⟨51552387440226532254024065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137473033173937419344064173 51552387440226532254024065)
    ·
      refine ⟨38664290580169899190518049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51552387440226532254024065 38664290580169899190518049)
      ·
        refine ⟨28998217935127424392888537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38664290580169899190518049 28998217935127424392888537)
        ·
          refine ⟨21748663451345568294666403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28998217935127424392888537 21748663451345568294666403)
          ·
            refine ⟨32622995177018352441999605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21748663451345568294666403 32622995177018352441999605)
            ·
              refine ⟨3058405797845470541437463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32622995177018352441999605 3058405797845470541437463)
              ·
                refine ⟨4587608696768205812156195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3058405797845470541437463 4587608696768205812156195)
                ·
                  refine ⟨6881413045152308718234293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4587608696768205812156195 6881413045152308718234293)
                  ·
                    refine ⟨645132472983028942334465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6881413045152308718234293 645132472983028942334465)
                    ·
                      rfl

theorem cell23_3769173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_3769173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769173 prefixEnd_3769173 := by exact prefixLift 3769173
  have htrace : WordTrace (prefixWord ++ tailWord_3769173) baseStart_3769173 baseEnd_3769173 := by
    simpa [prefixWord, tailWord_3769173, baseEnd_3769173] using wordTrace_append hprefix tailTrace_3769173
  have hstable : (prefixWord ++ tailWord_3769173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769173).length < 2 ^ (prefixWord ++ tailWord_3769173).sum := by decide
  have hdescent : baseEnd_3769173 < baseStart_3769173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769176 : List Nat := [2, 1, 2, 2, 1, 1, 1, 7, 1, 1, 4]
def baseStart_3769176 : Nat := 118140960795 + 3769176 * 2 ^ 59
def prefixEnd_3769176 : Nat := 4983230072969 + 3 ^ 40 * 3769176 * 2
def baseEnd_3769176 : Nat := 1935398959391050315265881

theorem tailTrace_3769176 : CollatzResearch.WordTrace tailWord_3769176 prefixEnd_3769176 1935398959391050315265881 := by
  unfold tailWord_3769176
  simp only [CollatzResearch.WordTrace]
  refine ⟨68736571296463275428211691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91648761728617700570948921 68736571296463275428211691)
  ·
    refine ⟨103104856944694913142317537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68736571296463275428211691 103104856944694913142317537)
    ·
      refine ⟨77328642708521184856738153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103104856944694913142317537 77328642708521184856738153)
      ·
        refine ⟨57996482031390888642553615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77328642708521184856738153 57996482031390888642553615)
        ·
          refine ⟨86994723047086332963830423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57996482031390888642553615 86994723047086332963830423)
          ·
            refine ⟨130492084570629499445745635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86994723047086332963830423 130492084570629499445745635)
            ·
              refine ⟨195738126855944249168618453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130492084570629499445745635 195738126855944249168618453)
              ·
                refine ⟨4587612348186193339889495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 195738126855944249168618453 4587612348186193339889495)
                ·
                  refine ⟨6881418522279290009834243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4587612348186193339889495 6881418522279290009834243)
                  ·
                    refine ⟨10322127783418935014751365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6881418522279290009834243 10322127783418935014751365)
                    ·
                      refine ⟨1935398959391050315265881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10322127783418935014751365 1935398959391050315265881)
                      ·
                        rfl

theorem cell23_3769176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_3769176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769176 prefixEnd_3769176 := by exact prefixLift 3769176
  have htrace : WordTrace (prefixWord ++ tailWord_3769176) baseStart_3769176 baseEnd_3769176 := by
    simpa [prefixWord, tailWord_3769176, baseEnd_3769176] using wordTrace_append hprefix tailTrace_3769176
  have hstable : (prefixWord ++ tailWord_3769176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769176).length < 2 ^ (prefixWord ++ tailWord_3769176).sum := by decide
  have hdescent : baseEnd_3769176 < baseStart_3769176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769179 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 3]
def baseStart_3769179 : Nat := 118140960795 + 3769179 * 2 ^ 59
def prefixEnd_3769179 : Nat := 4983230072969 + 3 ^ 40 * 3769179 * 2
def baseEnd_3769179 : Nat := 1935400499833013803528367

theorem tailTrace_3769179 : CollatzResearch.WordTrace tailWord_3769179 prefixEnd_3769179 1935400499833013803528367 := by
  unfold tailWord_3769179
  simp only [CollatzResearch.WordTrace]
  refine ⟨137473252011915682368782591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91648834674610454912521727 137473252011915682368782591)
  ·
    refine ⟨206209878017873523553173887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137473252011915682368782591 206209878017873523553173887)
    ·
      refine ⟨309314817026810285329760831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206209878017873523553173887 309314817026810285329760831)
      ·
        refine ⟨463972225540215427994641247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309314817026810285329760831 463972225540215427994641247)
        ·
          refine ⟨695958338310323141991961871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463972225540215427994641247 695958338310323141991961871)
          ·
            refine ⟨1043937507465484712987942807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695958338310323141991961871 1043937507465484712987942807)
            ·
              refine ⟨1565906261198227069481914211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1043937507465484712987942807 1565906261198227069481914211)
              ·
                refine ⟨2348859391797340604222871317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1565906261198227069481914211 2348859391797340604222871317)
                ·
                  refine ⟨110102783990500340822947093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2348859391797340604222871317 110102783990500340822947093)
                  ·
                    refine ⟨5161067999554703476075645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110102783990500340822947093 5161067999554703476075645)
                    ·
                      refine ⟨1935400499833013803528367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5161067999554703476075645 1935400499833013803528367)
                      ·
                        rfl

theorem cell23_3769179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 3].length) (baseStart_3769179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769179 prefixEnd_3769179 := by exact prefixLift 3769179
  have htrace : WordTrace (prefixWord ++ tailWord_3769179) baseStart_3769179 baseEnd_3769179 := by
    simpa [prefixWord, tailWord_3769179, baseEnd_3769179] using wordTrace_append hprefix tailTrace_3769179
  have hstable : (prefixWord ++ tailWord_3769179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769179).length < 2 ^ (prefixWord ++ tailWord_3769179).sum := by decide
  have hdescent : baseEnd_3769179 < baseStart_3769179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769180 : List Nat := [2, 2, 4, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_3769180 : Nat := 118140960795 + 3769180 * 2 ^ 59
def prefixEnd_3769180 : Nat := 4983230072969 + 3 ^ 40 * 3769180 * 2
def baseEnd_3769180 : Nat := 1935401013313668299615863

theorem tailTrace_3769180 : CollatzResearch.WordTrace tailWord_3769180 prefixEnd_3769180 1935401013313668299615863 := by
  unfold tailWord_3769180
  simp only [CollatzResearch.WordTrace]
  refine ⟨68736644242456029769784497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91648858989941373026379329 68736644242456029769784497)
  ·
    refine ⟨51552483181842022327338373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68736644242456029769784497 51552483181842022327338373)
    ·
      refine ⟨9666090596595379186375945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51552483181842022327338373 9666090596595379186375945)
      ·
        refine ⟨7249567947446534389781959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9666090596595379186375945 7249567947446534389781959)
        ·
          refine ⟨10874351921169801584672939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7249567947446534389781959 10874351921169801584672939)
          ·
            refine ⟨16311527881754702377009409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10874351921169801584672939 16311527881754702377009409)
            ·
              refine ⟨12233645911316026782757057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16311527881754702377009409 12233645911316026782757057)
              ·
                refine ⟨9175234433487020087067793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12233645911316026782757057 9175234433487020087067793)
                ·
                  refine ⟨6881425825115265065300845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9175234433487020087067793 6881425825115265065300845)
                  ·
                    refine ⟨2580534684418224399487817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6881425825115265065300845 2580534684418224399487817)
                    ·
                      refine ⟨1935401013313668299615863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2580534684418224399487817 1935401013313668299615863)
                      ·
                        rfl

theorem cell23_3769180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_3769180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769180 prefixEnd_3769180 := by exact prefixLift 3769180
  have htrace : WordTrace (prefixWord ++ tailWord_3769180) baseStart_3769180 baseEnd_3769180 := by
    simpa [prefixWord, tailWord_3769180, baseEnd_3769180] using wordTrace_append hprefix tailTrace_3769180
  have hstable : (prefixWord ++ tailWord_3769180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769180).length < 2 ^ (prefixWord ++ tailWord_3769180).sum := by decide
  have hdescent : baseEnd_3769180 < baseStart_3769180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769187 : List Nat := [1, 1, 1, 5, 3, 1, 4, 2, 1, 1, 3]
def baseStart_3769187 : Nat := 118140960795 + 3769187 * 2 ^ 59
def prefixEnd_3769187 : Nat := 4983230072969 + 3 ^ 40 * 3769187 * 2
def baseEnd_3769187 : Nat := 1935404607678249772228331

theorem tailTrace_3769187 : CollatzResearch.WordTrace tailWord_3769187 prefixEnd_3769187 1935404607678249772228331 := by
  unfold tailWord_3769187
  simp only [CollatzResearch.WordTrace]
  refine ⟨137473543795886699735073815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91649029197257799823382543 137473543795886699735073815)
  ·
    refine ⟨206210315693830049602610723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137473543795886699735073815 206210315693830049602610723)
    ·
      refine ⟨309315473540745074403916085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206210315693830049602610723 309315473540745074403916085)
      ·
        refine ⟨28998325644444850725367133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 309315473540745074403916085 28998325644444850725367133)
        ·
          refine ⟨10874372116666819022012675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28998325644444850725367133 10874372116666819022012675)
          ·
            refine ⟨16311558175000228533019013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10874372116666819022012675 16311558175000228533019013)
            ·
              refine ⟨3058417157812542849941065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16311558175000228533019013 3058417157812542849941065)
              ·
                refine ⟨2293812868359407137455799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3058417157812542849941065 2293812868359407137455799)
                ·
                  refine ⟨3440719302539110706183699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293812868359407137455799 3440719302539110706183699)
                  ·
                    refine ⟨5161078953808666059275549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3440719302539110706183699 5161078953808666059275549)
                    ·
                      refine ⟨1935404607678249772228331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5161078953808666059275549 1935404607678249772228331)
                      ·
                        rfl

theorem cell23_3769187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_3769187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769187 prefixEnd_3769187 := by exact prefixLift 3769187
  have htrace : WordTrace (prefixWord ++ tailWord_3769187) baseStart_3769187 baseEnd_3769187 := by
    simpa [prefixWord, tailWord_3769187, baseEnd_3769187] using wordTrace_append hprefix tailTrace_3769187
  have hstable : (prefixWord ++ tailWord_3769187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769187).length < 2 ^ (prefixWord ++ tailWord_3769187).sum := by decide
  have hdescent : baseEnd_3769187 < baseStart_3769187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769189 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 3, 1, 6]
def baseStart_3769189 : Nat := 118140960795 + 3769189 * 2 ^ 59
def prefixEnd_3769189 : Nat := 4983230072969 + 3 ^ 40 * 3769189 * 2
def baseEnd_3769189 : Nat := 1935405634639558764403321

theorem tailTrace_3769189 : CollatzResearch.WordTrace tailWord_3769189 prefixEnd_3769189 1935405634639558764403321 := by
  unfold tailWord_3769189
  simp only [CollatzResearch.WordTrace]
  refine ⟨137473616741879454076646621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91649077827919636051097747 137473616741879454076646621)
  ·
    refine ⟨51552606278204795278742483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137473616741879454076646621 51552606278204795278742483)
    ·
      refine ⟨77328909417307192918113725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51552606278204795278742483 77328909417307192918113725)
      ·
        refine ⟨28998341031490197344292647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77328909417307192918113725 28998341031490197344292647)
        ·
          refine ⟨43497511547235296016438971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28998341031490197344292647 43497511547235296016438971)
          ·
            refine ⟨65246267320852944024658457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43497511547235296016438971 65246267320852944024658457)
            ·
              refine ⟨48934700490639708018493843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65246267320852944024658457 48934700490639708018493843)
              ·
                refine ⟨73402050735959562027740765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48934700490639708018493843 73402050735959562027740765)
                ·
                  refine ⟨27525769025984835760402787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73402050735959562027740765 27525769025984835760402787)
                  ·
                    refine ⟨41288653538977253640604181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27525769025984835760402787 41288653538977253640604181)
                    ·
                      refine ⟨1935405634639558764403321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41288653538977253640604181 1935405634639558764403321)
                      ·
                        rfl

theorem cell23_3769189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_3769189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769189 prefixEnd_3769189 := by exact prefixLift 3769189
  have htrace : WordTrace (prefixWord ++ tailWord_3769189) baseStart_3769189 baseEnd_3769189 := by
    simpa [prefixWord, tailWord_3769189, baseEnd_3769189] using wordTrace_append hprefix tailTrace_3769189
  have hstable : (prefixWord ++ tailWord_3769189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769189).length < 2 ^ (prefixWord ++ tailWord_3769189).sum := by decide
  have hdescent : baseEnd_3769189 < baseStart_3769189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769196 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 3]
def baseStart_3769196 : Nat := 118140960795 + 3769196 * 2 ^ 59
def prefixEnd_3769196 : Nat := 4983230072969 + 3 ^ 40 * 3769196 * 2
def baseEnd_3769196 : Nat := 1935409229004140237015789

theorem tailTrace_3769196 : CollatzResearch.WordTrace tailWord_3769196 prefixEnd_3769196 1935409229004140237015789 := by
  unfold tailWord_3769196
  simp only [CollatzResearch.WordTrace]
  refine ⟨68736936026427047136075721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91649248035236062848100961 68736936026427047136075721)
  ·
    refine ⟨51552702019820285352056791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68736936026427047136075721 51552702019820285352056791)
    ·
      refine ⟨77329053029730428028085187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51552702019820285352056791 77329053029730428028085187)
      ·
        refine ⟨115993579544595642042127781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77329053029730428028085187 115993579544595642042127781)
        ·
          refine ⟨21748796164611682882898959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115993579544595642042127781 21748796164611682882898959)
          ·
            refine ⟨32623194246917524324348439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21748796164611682882898959 32623194246917524324348439)
            ·
              refine ⟨48934791370376286486522659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32623194246917524324348439 48934791370376286486522659)
              ·
                refine ⟨73402187055564429729783989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48934791370376286486522659 73402187055564429729783989)
                ·
                  refine ⟨6881455036459165287167249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73402187055564429729783989 6881455036459165287167249)
                  ·
                    refine ⟨5161091277344373965375437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6881455036459165287167249 5161091277344373965375437)
                    ·
                      refine ⟨1935409229004140237015789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5161091277344373965375437 1935409229004140237015789)
                      ·
                        rfl

theorem cell23_3769196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_3769196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769196 prefixEnd_3769196 := by exact prefixLift 3769196
  have htrace : WordTrace (prefixWord ++ tailWord_3769196) baseStart_3769196 baseEnd_3769196 := by
    simpa [prefixWord, tailWord_3769196, baseEnd_3769196] using wordTrace_append hprefix tailTrace_3769196
  have hstable : (prefixWord ++ tailWord_3769196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769196).length < 2 ^ (prefixWord ++ tailWord_3769196).sum := by decide
  have hdescent : baseEnd_3769196 < baseStart_3769196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769214 : List Nat := [4, 2, 3, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_3769214 : Nat := 118140960795 + 3769214 * 2 ^ 59
def prefixEnd_3769214 : Nat := 4983230072969 + 3 ^ 40 * 3769214 * 2
def baseEnd_3769214 : Nat := 1935418471655921166590707

theorem tailTrace_3769214 : CollatzResearch.WordTrace tailWord_3769214 prefixEnd_3769214 1935418471655921166590707 := by
  unfold tailWord_3769214
  simp only [CollatzResearch.WordTrace]
  refine ⟨17184316070848610418288337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91649685711192588897537797 17184316070848610418288337)
  ·
    refine ⟨12888237053136457813716253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17184316070848610418288337 12888237053136457813716253)
    ·
      refine ⟨4833088894926171680143595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12888237053136457813716253 4833088894926171680143595)
      ·
        refine ⟨7249633342389257520215393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4833088894926171680143595 7249633342389257520215393)
        ·
          refine ⟨5437225006791943140161545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7249633342389257520215393 5437225006791943140161545)
          ·
            refine ⟨4077918755093957355121159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5437225006791943140161545 4077918755093957355121159)
            ·
              refine ⟨6116878132640936032681739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4077918755093957355121159 6116878132640936032681739)
              ·
                refine ⟨9175317198961404049022609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6116878132640936032681739 9175317198961404049022609)
                ·
                  refine ⟨6881487899221053036766957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9175317198961404049022609 6881487899221053036766957)
                  ·
                    refine ⟨2580557962207894888787609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6881487899221053036766957 2580557962207894888787609)
                    ·
                      refine ⟨1935418471655921166590707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2580557962207894888787609 1935418471655921166590707)
                      ·
                        rfl

theorem cell23_3769214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_3769214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769214 prefixEnd_3769214 := by exact prefixLift 3769214
  have htrace : WordTrace (prefixWord ++ tailWord_3769214) baseStart_3769214 baseEnd_3769214 := by
    simpa [prefixWord, tailWord_3769214, baseEnd_3769214] using wordTrace_append hprefix tailTrace_3769214
  have hstable : (prefixWord ++ tailWord_3769214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769214).length < 2 ^ (prefixWord ++ tailWord_3769214).sum := by decide
  have hdescent : baseEnd_3769214 < baseStart_3769214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769390 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_3769390 : Nat := 118140960795 + 3769390 * 2 ^ 59
def prefixEnd_3769390 : Nat := 4983230072969 + 3 ^ 40 * 3769390 * 2
def baseEnd_3769390 : Nat := 1935508844251112477989897

theorem tailTrace_3769390 : CollatzResearch.WordTrace tailWord_3769390 prefixEnd_3769390 1935508844251112477989897 := by
  unfold tailWord_3769390
  simp only [CollatzResearch.WordTrace]
  refine ⟨17185118476768908175589203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91653965209434176936475749 17185118476768908175589203)
  ·
    refine ⟨25777677715153362263383805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17185118476768908175589203 25777677715153362263383805)
    ·
      refine ⟨9666629143182510848768927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25777677715153362263383805 9666629143182510848768927)
      ·
        refine ⟨14499943714773766273153391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9666629143182510848768927 14499943714773766273153391)
        ·
          refine ⟨21749915572160649409730087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14499943714773766273153391 21749915572160649409730087)
          ·
            refine ⟨32624873358240974114595131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21749915572160649409730087 32624873358240974114595131)
            ·
              refine ⟨48937310037361461171892697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32624873358240974114595131 48937310037361461171892697)
              ·
                refine ⟨36702982528021095878919523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48937310037361461171892697 36702982528021095878919523)
                ·
                  refine ⟨55054473792031643818379285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36702982528021095878919523 55054473792031643818379285)
                  ·
                    refine ⟨2580678459001483303986529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55054473792031643818379285 2580678459001483303986529)
                    ·
                      refine ⟨1935508844251112477989897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2580678459001483303986529 1935508844251112477989897)
                      ·
                        rfl

theorem cell23_3769390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_3769390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769390 prefixEnd_3769390 := by exact prefixLift 3769390
  have htrace : WordTrace (prefixWord ++ tailWord_3769390) baseStart_3769390 baseEnd_3769390 := by
    simpa [prefixWord, tailWord_3769390, baseEnd_3769390] using wordTrace_append hprefix tailTrace_3769390
  have hstable : (prefixWord ++ tailWord_3769390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769390).length < 2 ^ (prefixWord ++ tailWord_3769390).sum := by decide
  have hdescent : baseEnd_3769390 < baseStart_3769390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769393 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 1, 4, 3]
def baseStart_3769393 : Nat := 118140960795 + 3769393 * 2 ^ 59
def prefixEnd_3769393 : Nat := 4983230072969 + 3 ^ 40 * 3769393 * 2
def baseEnd_3769393 : Nat := 1935510384693075966252383

theorem tailTrace_3769393 : CollatzResearch.WordTrace tailWord_3769393 prefixEnd_3769393 1935510384693075966252383 := by
  unfold tailWord_3769393
  simp only [CollatzResearch.WordTrace]
  refine ⟨137481057233140396917072833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91654038155426931278048555 137481057233140396917072833)
  ·
    refine ⟨103110792924855297687804625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137481057233140396917072833 103110792924855297687804625)
    ·
      refine ⟨77333094693641473265853469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103110792924855297687804625 77333094693641473265853469)
      ·
        refine ⟨28999910510115552474695051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77333094693641473265853469 28999910510115552474695051)
        ·
          refine ⟨43499865765173328712042577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28999910510115552474695051 43499865765173328712042577)
          ·
            refine ⟨32624899323879996534031933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43499865765173328712042577 32624899323879996534031933)
            ·
              refine ⟨12234337246454998700261975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32624899323879996534031933 12234337246454998700261975)
              ·
                refine ⟨18351505869682498050392963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12234337246454998700261975 18351505869682498050392963)
                ·
                  refine ⟨27527258804523747075589445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18351505869682498050392963 27527258804523747075589445)
                  ·
                    refine ⟨5161361025848202576673021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27527258804523747075589445 5161361025848202576673021)
                    ·
                      refine ⟨1935510384693075966252383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5161361025848202576673021 1935510384693075966252383)
                      ·
                        rfl

theorem cell23_3769393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_3769393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769393 prefixEnd_3769393 := by exact prefixLift 3769393
  have htrace : WordTrace (prefixWord ++ tailWord_3769393) baseStart_3769393 baseEnd_3769393 := by
    simpa [prefixWord, tailWord_3769393, baseEnd_3769393] using wordTrace_append hprefix tailTrace_3769393
  have hstable : (prefixWord ++ tailWord_3769393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769393).length < 2 ^ (prefixWord ++ tailWord_3769393).sum := by decide
  have hdescent : baseEnd_3769393 < baseStart_3769393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769413 : List Nat := [1, 3, 1, 1, 1, 3, 5, 2, 6]
def baseStart_3769413 : Nat := 118140960795 + 3769413 * 2 ^ 59
def prefixEnd_3769413 : Nat := 4983230072969 + 3 ^ 40 * 3769413 * 2
def baseEnd_3769413 : Nat := 215057850478462876444699

theorem tailTrace_3769413 : CollatzResearch.WordTrace tailWord_3769413 prefixEnd_3769413 215057850478462876444699 := by
  unfold tailWord_3769413
  simp only [CollatzResearch.WordTrace]
  refine ⟨137481786693067940332800893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91654524462045293555200595 137481786693067940332800893)
  ·
    refine ⟨51555670009900477624800335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137481786693067940332800893 51555670009900477624800335)
    ·
      refine ⟨77333505014850716437200503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51555670009900477624800335 77333505014850716437200503)
      ·
        refine ⟨116000257522276074655800755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77333505014850716437200503 116000257522276074655800755)
        ·
          refine ⟨174000386283414111983701133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116000257522276074655800755 174000386283414111983701133)
          ·
            refine ⟨65250144856280291993887925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174000386283414111983701133 65250144856280291993887925)
            ·
              refine ⟨6117201080276277374426993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65250144856280291993887925 6117201080276277374426993)
              ·
                refine ⟨4587900810207208030820245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6117201080276277374426993 4587900810207208030820245)
                ·
                  refine ⟨215057850478462876444699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4587900810207208030820245 215057850478462876444699)
                  ·
                    rfl

theorem cell23_3769413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 6].length) (baseStart_3769413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769413 prefixEnd_3769413 := by exact prefixLift 3769413
  have htrace : WordTrace (prefixWord ++ tailWord_3769413) baseStart_3769413 baseEnd_3769413 := by
    simpa [prefixWord, tailWord_3769413, baseEnd_3769413] using wordTrace_append hprefix tailTrace_3769413
  have hstable : (prefixWord ++ tailWord_3769413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769413).length < 2 ^ (prefixWord ++ tailWord_3769413).sum := by decide
  have hdescent : baseEnd_3769413 < baseStart_3769413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769416 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_3769416 : Nat := 118140960795 + 3769416 * 2 ^ 59
def prefixEnd_3769416 : Nat := 4983230072969 + 3 ^ 40 * 3769416 * 2
def baseEnd_3769416 : Nat := 1935522194748129376264777

theorem tailTrace_3769416 : CollatzResearch.WordTrace tailWord_3769416 prefixEnd_3769416 1935522194748129376264777 := by
  unfold tailWord_3769416
  simp only [CollatzResearch.WordTrace]
  refine ⟨68740948056028535922580051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91654597408038047896773401 68740948056028535922580051)
  ·
    refine ⟨103111422084042803883870077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68740948056028535922580051 103111422084042803883870077)
    ·
      refine ⟨38666783281516051456451279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103111422084042803883870077 38666783281516051456451279)
      ·
        refine ⟨58000174922274077184676919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38666783281516051456451279 58000174922274077184676919)
        ·
          refine ⟨87000262383411115777015379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58000174922274077184676919 87000262383411115777015379)
          ·
            refine ⟨130500393575116673665523069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87000262383411115777015379 130500393575116673665523069)
            ·
              refine ⟨48937647590668752624571151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130500393575116673665523069 48937647590668752624571151)
              ·
                refine ⟨73406471386003128936856727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48937647590668752624571151 73406471386003128936856727)
                ·
                  refine ⟨110109707079004693405285091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73406471386003128936856727 110109707079004693405285091)
                  ·
                    refine ⟨165164560618507040107927637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110109707079004693405285091 165164560618507040107927637)
                    ·
                      refine ⟨1935522194748129376264777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 165164560618507040107927637 1935522194748129376264777)
                      ·
                        rfl

theorem cell23_3769416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_3769416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769416 prefixEnd_3769416 := by exact prefixLift 3769416
  have htrace : WordTrace (prefixWord ++ tailWord_3769416) baseStart_3769416 baseEnd_3769416 := by
    simpa [prefixWord, tailWord_3769416, baseEnd_3769416] using wordTrace_append hprefix tailTrace_3769416
  have hstable : (prefixWord ++ tailWord_3769416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769416).length < 2 ^ (prefixWord ++ tailWord_3769416).sum := by decide
  have hdescent : baseEnd_3769416 < baseStart_3769416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769440 : List Nat := [2, 1, 1, 3, 2, 2, 1, 4, 3, 1, 3]
def baseStart_3769440 : Nat := 118140960795 + 3769440 * 2 ^ 59
def prefixEnd_3769440 : Nat := 4983230072969 + 3 ^ 40 * 3769440 * 2
def baseEnd_3769440 : Nat := 1935534518283837282364667

theorem tailTrace_3769440 : CollatzResearch.WordTrace tailWord_3769440 prefixEnd_3769440 1935534518283837282364667 := by
  unfold tailWord_3769440
  simp only [CollatzResearch.WordTrace]
  refine ⟨68741385731985061972016887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91655180975980082629355849 68741385731985061972016887)
  ·
    refine ⟨103112078597977592958025331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68741385731985061972016887 103112078597977592958025331)
    ·
      refine ⟨154668117896966389437037997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103112078597977592958025331 154668117896966389437037997)
      ·
        refine ⟨58000544211362396038889249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154668117896966389437037997 58000544211362396038889249)
        ·
          refine ⟨43500408158521797029166937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58000544211362396038889249 43500408158521797029166937)
          ·
            refine ⟨32625306118891347771875203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43500408158521797029166937 32625306118891347771875203)
            ·
              refine ⟨48937959178337021657812805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32625306118891347771875203 48937959178337021657812805)
              ·
                refine ⟨9175867345938191560839901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48937959178337021657812805 9175867345938191560839901)
                ·
                  refine ⟨3440950254726821835314963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9175867345938191560839901 3440950254726821835314963)
                  ·
                    refine ⟨5161425382090232752972445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3440950254726821835314963 5161425382090232752972445)
                    ·
                      refine ⟨1935534518283837282364667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5161425382090232752972445 1935534518283837282364667)
                      ·
                        rfl

theorem cell23_3769440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_3769440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769440 prefixEnd_3769440 := by exact prefixLift 3769440
  have htrace : WordTrace (prefixWord ++ tailWord_3769440) baseStart_3769440 baseEnd_3769440 := by
    simpa [prefixWord, tailWord_3769440, baseEnd_3769440] using wordTrace_append hprefix tailTrace_3769440
  have hstable : (prefixWord ++ tailWord_3769440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769440).length < 2 ^ (prefixWord ++ tailWord_3769440).sum := by decide
  have hdescent : baseEnd_3769440 < baseStart_3769440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769457 : List Nat := [1, 2, 2, 2, 1, 1, 2, 7, 1, 1, 3]
def baseStart_3769457 : Nat := 118140960795 + 3769457 * 2 ^ 59
def prefixEnd_3769457 : Nat := 4983230072969 + 3 ^ 40 * 3769457 * 2
def baseEnd_3769457 : Nat := 1935543247454963715852089

theorem tailTrace_3769457 : CollatzResearch.WordTrace tailWord_3769457 prefixEnd_3769457 1935543247454963715852089 := by
  unfold tailWord_3769457
  simp only [CollatzResearch.WordTrace]
  refine ⟨137483391504908535847402625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91655594336605690564935083 137483391504908535847402625)
  ·
    refine ⟨103112543628681401885551969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137483391504908535847402625 103112543628681401885551969)
    ·
      refine ⟨77334407721511051414163977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103112543628681401885551969 77334407721511051414163977)
      ·
        refine ⟨58000805791133288560622983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77334407721511051414163977 58000805791133288560622983)
        ·
          refine ⟨87001208686699932840934475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58000805791133288560622983 87001208686699932840934475)
          ·
            refine ⟨130501813030049899261401713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87001208686699932840934475 130501813030049899261401713)
            ·
              refine ⟨97876359772537424446051285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130501813030049899261401713 97876359772537424446051285)
              ·
                refine ⟨2293977182168845885454327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 97876359772537424446051285 2293977182168845885454327)
                ·
                  refine ⟨3440965773253268828181491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293977182168845885454327 3440965773253268828181491)
                  ·
                    refine ⟨5161448659879903242272237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3440965773253268828181491 5161448659879903242272237)
                    ·
                      refine ⟨1935543247454963715852089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5161448659879903242272237 1935543247454963715852089)
                      ·
                        rfl

theorem cell23_3769457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_3769457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769457 prefixEnd_3769457 := by exact prefixLift 3769457
  have htrace : WordTrace (prefixWord ++ tailWord_3769457) baseStart_3769457 baseEnd_3769457 := by
    simpa [prefixWord, tailWord_3769457, baseEnd_3769457] using wordTrace_append hprefix tailTrace_3769457
  have hstable : (prefixWord ++ tailWord_3769457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769457).length < 2 ^ (prefixWord ++ tailWord_3769457).sum := by decide
  have hdescent : baseEnd_3769457 < baseStart_3769457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769533 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 2, 7]
def baseStart_3769533 : Nat := 118140960795 + 3769533 * 2 ^ 59
def prefixEnd_3769533 : Nat := 4983230072969 + 3 ^ 40 * 3769533 * 2
def baseEnd_3769533 : Nat := 645194090661568472833913

theorem tailTrace_3769533 : CollatzResearch.WordTrace tailWord_3769533 prefixEnd_3769533 645194090661568472833913 := by
  unfold tailWord_3769533
  simp only [CollatzResearch.WordTrace]
  refine ⟨137486163452633200827169253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91657442301755467218112835 137486163452633200827169253)
  ·
    refine ⟨25778655647368725155094235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137486163452633200827169253 25778655647368725155094235)
    ·
      refine ⟨38667983471053087732641353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25778655647368725155094235 38667983471053087732641353)
      ·
        refine ⟨29000987603289815799481015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38667983471053087732641353 29000987603289815799481015)
        ·
          refine ⟨43501481404934723699221523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29000987603289815799481015 43501481404934723699221523)
          ·
            refine ⟨65252222107402085548832285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43501481404934723699221523 65252222107402085548832285)
            ·
              refine ⟨24469583290275782080812107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65252222107402085548832285 24469583290275782080812107)
              ·
                refine ⟨36704374935413673121218161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24469583290275782080812107 36704374935413673121218161)
                ·
                  refine ⟨27528281201560254840913621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36704374935413673121218161 27528281201560254840913621)
                  ·
                    refine ⟨645194090661568472833913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27528281201560254840913621 645194090661568472833913)
                    ·
                      rfl

theorem cell23_3769533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_3769533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769533 prefixEnd_3769533 := by exact prefixLift 3769533
  have htrace : WordTrace (prefixWord ++ tailWord_3769533) baseStart_3769533 baseEnd_3769533 := by
    simpa [prefixWord, tailWord_3769533, baseEnd_3769533] using wordTrace_append hprefix tailTrace_3769533
  have hstable : (prefixWord ++ tailWord_3769533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769533).length < 2 ^ (prefixWord ++ tailWord_3769533).sum := by decide
  have hdescent : baseEnd_3769533 < baseStart_3769533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769537 : List Nat := [1, 2, 6, 1, 1, 3, 1, 8]
def baseStart_3769537 : Nat := 118140960795 + 3769537 * 2 ^ 59
def prefixEnd_3769537 : Nat := 4983230072969 + 3 ^ 40 * 3769537 * 2
def baseEnd_3769537 : Nat := 71688308366937903809323

theorem tailTrace_3769537 : CollatzResearch.WordTrace tailWord_3769537 prefixEnd_3769537 71688308366937903809323 := by
  unfold tailWord_3769537
  simp only [CollatzResearch.WordTrace]
  refine ⟨137486309344618709510314865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91657539563079139673543243 137486309344618709510314865)
  ·
    refine ⟨103114732008464032132736149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137486309344618709510314865 103114732008464032132736149)
    ·
      refine ⟨4833503062896751506222007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103114732008464032132736149 4833503062896751506222007)
      ·
        refine ⟨7250254594345127259333011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4833503062896751506222007 7250254594345127259333011)
        ·
          refine ⟨10875381891517690888999517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7250254594345127259333011 10875381891517690888999517)
          ·
            refine ⟨4078268209319134083374819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10875381891517690888999517 4078268209319134083374819)
            ·
              refine ⟨6117402313978701125062229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4078268209319134083374819 6117402313978701125062229)
              ·
                refine ⟨71688308366937903809323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6117402313978701125062229 71688308366937903809323)
                ·
                  rfl

theorem cell23_3769537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 8].length) (baseStart_3769537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769537 prefixEnd_3769537 := by exact prefixLift 3769537
  have htrace : WordTrace (prefixWord ++ tailWord_3769537) baseStart_3769537 baseEnd_3769537 := by
    simpa [prefixWord, tailWord_3769537, baseEnd_3769537] using wordTrace_append hprefix tailTrace_3769537
  have hstable : (prefixWord ++ tailWord_3769537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769537).length < 2 ^ (prefixWord ++ tailWord_3769537).sum := by decide
  have hdescent : baseEnd_3769537 < baseStart_3769537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769553 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 4, 3, 4]
def baseStart_3769553 : Nat := 118140960795 + 3769553 * 2 ^ 59
def prefixEnd_3769553 : Nat := 4983230072969 + 3 ^ 40 * 3769553 * 2
def baseEnd_3769553 : Nat := 1935592541597795340251647

theorem tailTrace_3769553 : CollatzResearch.WordTrace tailWord_3769553 prefixEnd_3769553 1935592541597795340251647 := by
  unfold tailWord_3769553
  simp only [CollatzResearch.WordTrace]
  refine ⟨137486892912560744242897313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91657928608373829495264875 137486892912560744242897313)
  ·
    refine ⟨103115169684420558182172985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137486892912560744242897313 103115169684420558182172985)
    ·
      refine ⟨77336377263315418636629739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103115169684420558182172985 77336377263315418636629739)
      ·
        refine ⟨116004565894973127954944609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77336377263315418636629739 116004565894973127954944609)
        ·
          refine ⟨87003424421229845966208457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116004565894973127954944609 87003424421229845966208457)
          ·
            refine ⟨65252568315922384474656343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87003424421229845966208457 65252568315922384474656343)
            ·
              refine ⟨97878852473883576711984515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65252568315922384474656343 97878852473883576711984515)
              ·
                refine ⟨146818278710825365067976773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97878852473883576711984515 146818278710825365067976773)
                ·
                  refine ⟨27528427258279755950245645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146818278710825365067976773 27528427258279755950245645)
                  ·
                    refine ⟨10323160221854908481342117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27528427258279755950245645 10323160221854908481342117)
                    ·
                      refine ⟨1935592541597795340251647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10323160221854908481342117 1935592541597795340251647)
                      ·
                        rfl

theorem cell23_3769553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_3769553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769553 prefixEnd_3769553 := by exact prefixLift 3769553
  have htrace : WordTrace (prefixWord ++ tailWord_3769553) baseStart_3769553 baseEnd_3769553 := by
    simpa [prefixWord, tailWord_3769553, baseEnd_3769553] using wordTrace_append hprefix tailTrace_3769553
  have hstable : (prefixWord ++ tailWord_3769553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769553).length < 2 ^ (prefixWord ++ tailWord_3769553).sum := by decide
  have hdescent : baseEnd_3769553 < baseStart_3769553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769581 : List Nat := [1, 5, 1, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_3769581 : Nat := 118140960795 + 3769581 * 2 ^ 59
def prefixEnd_3769581 : Nat := 4983230072969 + 3 ^ 40 * 3769581 * 2
def baseEnd_3769581 : Nat := 1935606919056121230701519

theorem tailTrace_3769581 : CollatzResearch.WordTrace tailWord_3769581 prefixEnd_3769581 1935606919056121230701519 := by
  unfold tailWord_3769581
  simp only [CollatzResearch.WordTrace]
  refine ⟨137487914156459305024916597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91658609437639536683277731 137487914156459305024916597)
  ·
    refine ⟨12889491952168059846085931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137487914156459305024916597 12889491952168059846085931)
    ·
      refine ⟨19334237928252089769128897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12889491952168059846085931 19334237928252089769128897)
      ·
        refine ⟨14500678446189067326846673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19334237928252089769128897 14500678446189067326846673)
        ·
          refine ⟨10875508834641800495135005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14500678446189067326846673 10875508834641800495135005)
          ·
            refine ⟨4078315812990675185675627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10875508834641800495135005 4078315812990675185675627)
            ·
              refine ⟨6117473719486012778513441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4078315812990675185675627 6117473719486012778513441)
              ·
                refine ⟨4588105289614509583885081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6117473719486012778513441 4588105289614509583885081)
                ·
                  refine ⟨3441078967210882187913811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4588105289614509583885081 3441078967210882187913811)
                  ·
                    refine ⟨5161618450816323281870717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3441078967210882187913811 5161618450816323281870717)
                    ·
                      refine ⟨1935606919056121230701519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5161618450816323281870717 1935606919056121230701519)
                      ·
                        rfl

theorem cell23_3769581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_3769581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769581 prefixEnd_3769581 := by exact prefixLift 3769581
  have htrace : WordTrace (prefixWord ++ tailWord_3769581) baseStart_3769581 baseEnd_3769581 := by
    simpa [prefixWord, tailWord_3769581, baseEnd_3769581] using wordTrace_append hprefix tailTrace_3769581
  have hstable : (prefixWord ++ tailWord_3769581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769581).length < 2 ^ (prefixWord ++ tailWord_3769581).sum := by decide
  have hdescent : baseEnd_3769581 < baseStart_3769581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769590 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_3769590 : Nat := 118140960795 + 3769590 * 2 ^ 59
def prefixEnd_3769590 : Nat := 4983230072969 + 3 ^ 40 * 3769590 * 2
def baseEnd_3769590 : Nat := 1935611540382011695488977

theorem tailTrace_3769590 : CollatzResearch.WordTrace tailWord_3769590 prefixEnd_3769590 1935611540382011695488977 := by
  unfold tailWord_3769590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8593015150839168722624639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91658828275617799707996149 8593015150839168722624639)
  ·
    refine ⟨12889522726258753083936959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8593015150839168722624639 12889522726258753083936959)
    ·
      refine ⟨19334284089388129625905439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12889522726258753083936959 19334284089388129625905439)
      ·
        refine ⟨29001426134082194438858159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19334284089388129625905439 29001426134082194438858159)
        ·
          refine ⟨43502139201123291658287239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29001426134082194438858159 43502139201123291658287239)
          ·
            refine ⟨65253208801684937487430859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43502139201123291658287239 65253208801684937487430859)
            ·
              refine ⟨97879813202527406231146289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65253208801684937487430859 97879813202527406231146289)
              ·
                refine ⟨73409859901895554673359717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97879813202527406231146289 73409859901895554673359717)
                ·
                  refine ⟨13764348731605416501254947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73409859901895554673359717 13764348731605416501254947)
                  ·
                    refine ⟨20646523097408124751882421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13764348731605416501254947 20646523097408124751882421)
                    ·
                      refine ⟨1935611540382011695488977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20646523097408124751882421 1935611540382011695488977)
                      ·
                        rfl

theorem cell23_3769590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_3769590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769590 prefixEnd_3769590 := by exact prefixLift 3769590
  have htrace : WordTrace (prefixWord ++ tailWord_3769590) baseStart_3769590 baseEnd_3769590 := by
    simpa [prefixWord, tailWord_3769590, baseEnd_3769590] using wordTrace_append hprefix tailTrace_3769590
  have hstable : (prefixWord ++ tailWord_3769590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769590).length < 2 ^ (prefixWord ++ tailWord_3769590).sum := by decide
  have hdescent : baseEnd_3769590 < baseStart_3769590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769604 : List Nat := [2, 3, 2, 2, 2, 1, 3, 1, 1, 4, 2]
def baseStart_3769604 : Nat := 118140960795 + 3769604 * 2 ^ 59
def prefixEnd_3769604 : Nat := 4983230072969 + 3 ^ 40 * 3769604 * 2
def baseEnd_3769604 : Nat := 1935618729111174640713913

theorem tailTrace_3769604 : CollatzResearch.WordTrace tailWord_3769604 prefixEnd_3769604 1935618729111174640713913 := by
  unfold tailWord_3769604
  simp only [CollatzResearch.WordTrace]
  refine ⟨68744376517687989976501933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91659168690250653302002577 68744376517687989976501933)
  ·
    refine ⟨25779141194132996241188225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68744376517687989976501933 25779141194132996241188225)
    ·
      refine ⟨19334355895599747180891169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25779141194132996241188225 19334355895599747180891169)
      ·
        refine ⟨14500766921699810385668377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19334355895599747180891169 14500766921699810385668377)
        ·
          refine ⟨10875575191274857789251283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14500766921699810385668377 10875575191274857789251283)
          ·
            refine ⟨16313362786912286683876925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10875575191274857789251283 16313362786912286683876925)
            ·
              refine ⟨6117511045092107506453847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16313362786912286683876925 6117511045092107506453847)
              ·
                refine ⟨9176266567638161259680771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6117511045092107506453847 9176266567638161259680771)
                ·
                  refine ⟨13764399851457241889521157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9176266567638161259680771 13764399851457241889521157)
                  ·
                    refine ⟨2580824972148232854285217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13764399851457241889521157 2580824972148232854285217)
                    ·
                      refine ⟨1935618729111174640713913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2580824972148232854285217 1935618729111174640713913)
                      ·
                        rfl

theorem cell23_3769604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_3769604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769604 prefixEnd_3769604 := by exact prefixLift 3769604
  have htrace : WordTrace (prefixWord ++ tailWord_3769604) baseStart_3769604 baseEnd_3769604 := by
    simpa [prefixWord, tailWord_3769604, baseEnd_3769604] using wordTrace_append hprefix tailTrace_3769604
  have hstable : (prefixWord ++ tailWord_3769604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769604).length < 2 ^ (prefixWord ++ tailWord_3769604).sum := by decide
  have hdescent : baseEnd_3769604 < baseStart_3769604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769650 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_3769650 : Nat := 118140960795 + 3769650 * 2 ^ 59
def prefixEnd_3769650 : Nat := 4983230072969 + 3 ^ 40 * 3769650 * 2
def baseEnd_3769650 : Nat := 1935642349221281460738701

theorem tailTrace_3769650 : CollatzResearch.WordTrace tailWord_3769650 prefixEnd_3769650 1935642349221281460738701 := by
  unfold tailWord_3769650
  simp only [CollatzResearch.WordTrace]
  refine ⟨34372607698302332452294601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91660287195472886539452269 34372607698302332452294601)
  ·
    refine ⟨25779455773726749339220951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34372607698302332452294601 25779455773726749339220951)
    ·
      refine ⟨38669183660590124008831427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25779455773726749339220951 38669183660590124008831427)
      ·
        refine ⟨58003775490885186013247141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38669183660590124008831427 58003775490885186013247141)
        ·
          refine ⟨10875707904540972377483839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58003775490885186013247141 10875707904540972377483839)
          ·
            refine ⟨16313561856811458566225759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10875707904540972377483839 16313561856811458566225759)
            ·
              refine ⟨24470342785217187849338639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16313561856811458566225759 24470342785217187849338639)
              ·
                refine ⟨36705514177825781774007959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24470342785217187849338639 36705514177825781774007959)
                ·
                  refine ⟨55058271266738672661011939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36705514177825781774007959 55058271266738672661011939)
                  ·
                    refine ⟨82587406900108008991517909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55058271266738672661011939 82587406900108008991517909)
                    ·
                      refine ⟨1935642349221281460738701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82587406900108008991517909 1935642349221281460738701)
                      ·
                        rfl

theorem cell23_3769650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_3769650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769650 prefixEnd_3769650 := by exact prefixLift 3769650
  have htrace : WordTrace (prefixWord ++ tailWord_3769650) baseStart_3769650 baseEnd_3769650 := by
    simpa [prefixWord, tailWord_3769650, baseEnd_3769650] using wordTrace_append hprefix tailTrace_3769650
  have hstable : (prefixWord ++ tailWord_3769650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769650).length < 2 ^ (prefixWord ++ tailWord_3769650).sum := by decide
  have hdescent : baseEnd_3769650 < baseStart_3769650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769754 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2]
def baseStart_3769754 : Nat := 118140960795 + 3769754 * 2 ^ 59
def prefixEnd_3769754 : Nat := 4983230072969 + 3 ^ 40 * 3769754 * 2
def baseEnd_3769754 : Nat := 1935695751209349053838223

theorem tailTrace_3769754 : CollatzResearch.WordTrace tailWord_3769754 prefixEnd_3769754 1935695751209349053838223 := by
  unfold tailWord_3769754
  simp only [CollatzResearch.WordTrace]
  refine ⟨34373555996208138892741079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91662815989888370380642877 34373555996208138892741079)
  ·
    refine ⟨51560333994312208339111619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34373555996208138892741079 51560333994312208339111619)
    ·
      refine ⟨77340500991468312508667429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51560333994312208339111619 77340500991468312508667429)
      ·
        refine ⟨14501343935900308595375143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77340500991468312508667429 14501343935900308595375143)
        ·
          refine ⟨21752015903850462893062715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14501343935900308595375143 21752015903850462893062715)
          ·
            refine ⟨32628023855775694339594073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21752015903850462893062715 32628023855775694339594073)
            ·
              refine ⟨24471017891831770754695555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32628023855775694339594073 24471017891831770754695555)
              ·
                refine ⟨36706526837747656132043333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24471017891831770754695555 36706526837747656132043333)
                ·
                  refine ⟨6882473782077685524758125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36706526837747656132043333 6882473782077685524758125)
                  ·
                    refine ⟨2580927668279132071784297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6882473782077685524758125 2580927668279132071784297)
                    ·
                      refine ⟨1935695751209349053838223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2580927668279132071784297 1935695751209349053838223)
                      ·
                        rfl

theorem cell23_3769754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_3769754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769754 prefixEnd_3769754 := by exact prefixLift 3769754
  have htrace : WordTrace (prefixWord ++ tailWord_3769754) baseStart_3769754 baseEnd_3769754 := by
    simpa [prefixWord, tailWord_3769754, baseEnd_3769754] using wordTrace_append hprefix tailTrace_3769754
  have hstable : (prefixWord ++ tailWord_3769754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769754).length < 2 ^ (prefixWord ++ tailWord_3769754).sum := by decide
  have hdescent : baseEnd_3769754 < baseStart_3769754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769804 : List Nat := [2, 2, 1, 4, 2, 2, 2, 1, 1, 1, 5]
def baseStart_3769804 : Nat := 118140960795 + 3769804 * 2 ^ 59
def prefixEnd_3769804 : Nat := 4983230072969 + 3 ^ 40 * 3769804 * 2
def baseEnd_3769804 : Nat := 1935721425242073858212993

theorem tailTrace_3769804 : CollatzResearch.WordTrace tailWord_3769804 prefixEnd_3769804 1935721425242073858212993 := by
  unfold tailWord_3769804
  simp only [CollatzResearch.WordTrace]
  refine ⟨68748023817325707055142233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91664031756434276073522977 68748023817325707055142233)
  ·
    refine ⟨51561017862994280291356675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68748023817325707055142233 51561017862994280291356675)
    ·
      refine ⟨77341526794491420437035013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51561017862994280291356675 77341526794491420437035013)
      ·
        refine ⟨14501536273967141331944065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77341526794491420437035013 14501536273967141331944065)
        ·
          refine ⟨10876152205475355998958049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14501536273967141331944065 10876152205475355998958049)
          ·
            refine ⟨8157114154106516999218537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10876152205475355998958049 8157114154106516999218537)
            ·
              refine ⟨6117835615579887749413903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8157114154106516999218537 6117835615579887749413903)
              ·
                refine ⟨9176753423369831624120855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6117835615579887749413903 9176753423369831624120855)
                ·
                  refine ⟨13765130135054747436181283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9176753423369831624120855 13765130135054747436181283)
                  ·
                    refine ⟨20647695202582121154271925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13765130135054747436181283 20647695202582121154271925)
                    ·
                      refine ⟨1935721425242073858212993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20647695202582121154271925 1935721425242073858212993)
                      ·
                        rfl

theorem cell23_3769804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_3769804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769804 prefixEnd_3769804 := by exact prefixLift 3769804
  have htrace : WordTrace (prefixWord ++ tailWord_3769804) baseStart_3769804 baseEnd_3769804 := by
    simpa [prefixWord, tailWord_3769804, baseEnd_3769804] using wordTrace_append hprefix tailTrace_3769804
  have hstable : (prefixWord ++ tailWord_3769804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769804).length < 2 ^ (prefixWord ++ tailWord_3769804).sum := by decide
  have hdescent : baseEnd_3769804 < baseStart_3769804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769814 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3769814 : Nat := 118140960795 + 3769814 * 2 ^ 59
def prefixEnd_3769814 : Nat := 4983230072969 + 3 ^ 40 * 3769814 * 2
def baseEnd_3769814 : Nat := 1935726560048618819087947

theorem tailTrace_3769814 : CollatzResearch.WordTrace tailWord_3769814 prefixEnd_3769814 1935726560048618819087947 := by
  unfold tailWord_3769814
  simp only [CollatzResearch.WordTrace]
  refine ⟨8593525772788449113634281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91664274909743457212098997 8593525772788449113634281)
  ·
    refine ⟨6445144329591336835225711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8593525772788449113634281 6445144329591336835225711)
    ·
      refine ⟨9667716494387005252838567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6445144329591336835225711 9667716494387005252838567)
      ·
        refine ⟨14501574741580507879257851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9667716494387005252838567 14501574741580507879257851)
        ·
          refine ⟨21752362112370761818886777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14501574741580507879257851 21752362112370761818886777)
          ·
            refine ⟨16314271584278071364165083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21752362112370761818886777 16314271584278071364165083)
            ·
              refine ⟨24471407376417107046247625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16314271584278071364165083 24471407376417107046247625)
              ·
                refine ⟨18353555532312830284685719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24471407376417107046247625 18353555532312830284685719)
                ·
                  refine ⟨27530333298469245427028579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18353555532312830284685719 27530333298469245427028579)
                  ·
                    refine ⟨41295499947703868140542869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27530333298469245427028579 41295499947703868140542869)
                    ·
                      refine ⟨1935726560048618819087947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41295499947703868140542869 1935726560048618819087947)
                      ·
                        rfl

theorem cell23_3769814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3769814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769814 prefixEnd_3769814 := by exact prefixLift 3769814
  have htrace : WordTrace (prefixWord ++ tailWord_3769814) baseStart_3769814 baseEnd_3769814 := by
    simpa [prefixWord, tailWord_3769814, baseEnd_3769814] using wordTrace_append hprefix tailTrace_3769814
  have hstable : (prefixWord ++ tailWord_3769814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769814).length < 2 ^ (prefixWord ++ tailWord_3769814).sum := by decide
  have hdescent : baseEnd_3769814 < baseStart_3769814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769818 : List Nat := [3, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2]
def baseStart_3769818 : Nat := 118140960795 + 3769818 * 2 ^ 59
def prefixEnd_3769818 : Nat := 4983230072969 + 3 ^ 40 * 3769818 * 2
def baseEnd_3769818 : Nat := 1935728613971236803437929

theorem tailTrace_3769818 : CollatzResearch.WordTrace tailWord_3769818 prefixEnd_3769818 1935728613971236803437929 := by
  unfold tailWord_3769818
  simp only [CollatzResearch.WordTrace]
  refine ⟨34374139564150173625323527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91664372171067129667529405 34374139564150173625323527)
  ·
    refine ⟨51561209346225260437985291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34374139564150173625323527 51561209346225260437985291)
    ·
      refine ⟨77341814019337890656977937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51561209346225260437985291 77341814019337890656977937)
      ·
        refine ⟨58006360514503417992733453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77341814019337890656977937 58006360514503417992733453)
        ·
          refine ⟨21752385192938781747275045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58006360514503417992733453 21752385192938781747275045)
          ·
            refine ⟨4078572223676021577614071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21752385192938781747275045 4078572223676021577614071)
            ·
              refine ⟨6117858335514032366421107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4078572223676021577614071 6117858335514032366421107)
              ·
                refine ⟨9176787503271048549631661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6117858335514032366421107 9176787503271048549631661)
                ·
                  refine ⟨3441295313726643206111873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9176787503271048549631661 3441295313726643206111873)
                  ·
                    refine ⟨2580971485294982404583905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3441295313726643206111873 2580971485294982404583905)
                    ·
                      refine ⟨1935728613971236803437929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2580971485294982404583905 1935728613971236803437929)
                      ·
                        rfl

theorem cell23_3769818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_3769818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769818 prefixEnd_3769818 := by exact prefixLift 3769818
  have htrace : WordTrace (prefixWord ++ tailWord_3769818) baseStart_3769818 baseEnd_3769818 := by
    simpa [prefixWord, tailWord_3769818, baseEnd_3769818] using wordTrace_append hprefix tailTrace_3769818
  have hstable : (prefixWord ++ tailWord_3769818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769818).length < 2 ^ (prefixWord ++ tailWord_3769818).sum := by decide
  have hdescent : baseEnd_3769818 < baseStart_3769818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769862 : List Nat := [6, 2, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_3769862 : Nat := 118140960795 + 3769862 * 2 ^ 59
def prefixEnd_3769862 : Nat := 4983230072969 + 3 ^ 40 * 3769862 * 2
def baseEnd_3769862 : Nat := 645250402373344877095909

theorem tailTrace_3769862 : CollatzResearch.WordTrace tailWord_3769862 prefixEnd_3769862 645250402373344877095909 := by
  unfold tailWord_3769862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4296817595888790312996745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91665442045627526677263893 4296817595888790312996745)
  ·
    refine ⟨3222613196916592734747559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4296817595888790312996745 3222613196916592734747559)
    ·
      refine ⟨4833919795374889102121339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3222613196916592734747559 4833919795374889102121339)
      ·
        refine ⟨7250879693062333653182009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4833919795374889102121339 7250879693062333653182009)
        ·
          refine ⟨5438159769796750239886507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7250879693062333653182009 5438159769796750239886507)
          ·
            refine ⟨8157239654695125359829761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5438159769796750239886507 8157239654695125359829761)
            ·
              refine ⟨6117929741021344019872321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8157239654695125359829761 6117929741021344019872321)
              ·
                refine ⟨4588447305766008014904241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6117929741021344019872321 4588447305766008014904241)
                ·
                  refine ⟨3441335479324506011178181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4588447305766008014904241 3441335479324506011178181)
                  ·
                    refine ⟨645250402373344877095909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3441335479324506011178181 645250402373344877095909)
                    ·
                      rfl

theorem cell23_3769862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_3769862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769862 prefixEnd_3769862 := by exact prefixLift 3769862
  have htrace : WordTrace (prefixWord ++ tailWord_3769862) baseStart_3769862 baseEnd_3769862 := by
    simpa [prefixWord, tailWord_3769862, baseEnd_3769862] using wordTrace_append hprefix tailTrace_3769862
  have hstable : (prefixWord ++ tailWord_3769862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769862).length < 2 ^ (prefixWord ++ tailWord_3769862).sum := by decide
  have hdescent : baseEnd_3769862 < baseStart_3769862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769868 : List Nat := [2, 2, 1, 2, 5, 1, 2, 2, 2, 1, 3]
def baseStart_3769868 : Nat := 118140960795 + 3769868 * 2 ^ 59
def prefixEnd_3769868 : Nat := 4983230072969 + 3 ^ 40 * 3769868 * 2
def baseEnd_3769868 : Nat := 1935754288003961607812699

theorem tailTrace_3769868 : CollatzResearch.WordTrace tailWord_3769868 prefixEnd_3769868 1935754288003961607812699 := by
  unfold tailWord_3769868
  simp only [CollatzResearch.WordTrace]
  refine ⟨68749190953209776520307129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91665587937613035360409505 68749190953209776520307129)
  ·
    refine ⟨51561893214907332390230347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68749190953209776520307129 51561893214907332390230347)
    ·
      refine ⟨77342839822360998585345521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51561893214907332390230347 77342839822360998585345521)
      ·
        refine ⟨58007129866770748939009141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77342839822360998585345521 58007129866770748939009141)
        ·
          refine ⟨5438168425009757713032107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58007129866770748939009141 5438168425009757713032107)
          ·
            refine ⟨8157252637514636569548161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5438168425009757713032107 8157252637514636569548161)
            ·
              refine ⟨6117939478135977427161121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8157252637514636569548161 6117939478135977427161121)
              ·
                refine ⟨4588454608601983070370841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6117939478135977427161121 4588454608601983070370841)
                ·
                  refine ⟨3441340956451487302778131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4588454608601983070370841 3441340956451487302778131)
                  ·
                    refine ⟨5162011434677230954167197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3441340956451487302778131 5162011434677230954167197)
                    ·
                      refine ⟨1935754288003961607812699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5162011434677230954167197 1935754288003961607812699)
                      ·
                        rfl

theorem cell23_3769868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_3769868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769868 prefixEnd_3769868 := by exact prefixLift 3769868
  have htrace : WordTrace (prefixWord ++ tailWord_3769868) baseStart_3769868 baseEnd_3769868 := by
    simpa [prefixWord, tailWord_3769868, baseEnd_3769868] using wordTrace_append hprefix tailTrace_3769868
  have hstable : (prefixWord ++ tailWord_3769868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769868).length < 2 ^ (prefixWord ++ tailWord_3769868).sum := by decide
  have hdescent : baseEnd_3769868 < baseStart_3769868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769869 : List Nat := [1, 7, 1, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_3769869 : Nat := 118140960795 + 3769869 * 2 ^ 59
def prefixEnd_3769869 : Nat := 4983230072969 + 3 ^ 40 * 3769869 * 2
def baseEnd_3769869 : Nat := 1935754801484616103900195

theorem tailTrace_3769869 : CollatzResearch.WordTrace tailWord_3769869 prefixEnd_3769869 1935754801484616103900195 := by
  unfold tailWord_3769869
  simp only [CollatzResearch.WordTrace]
  refine ⟨137498418379415930211400661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91665612252943953474267107 137498418379415930211400661)
  ·
    refine ⟨3222619180767560864329703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 137498418379415930211400661 3222619180767560864329703)
    ·
      refine ⟨4833928771151341296494555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3222619180767560864329703 4833928771151341296494555)
      ·
        refine ⟨7250893156727011944741833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4833928771151341296494555 7250893156727011944741833)
        ·
          refine ⟨5438169867545258958556375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7250893156727011944741833 5438169867545258958556375)
          ·
            refine ⟨8157254801317888437834563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5438169867545258958556375 8157254801317888437834563)
            ·
              refine ⟨12235882201976832656751845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8157254801317888437834563 12235882201976832656751845)
              ·
                refine ⟨2294227912870656123140971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12235882201976832656751845 2294227912870656123140971)
                ·
                  refine ⟨3441341869305984184711457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2294227912870656123140971 3441341869305984184711457)
                  ·
                    refine ⟨2581006401979488138533593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3441341869305984184711457 2581006401979488138533593)
                    ·
                      refine ⟨1935754801484616103900195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2581006401979488138533593 1935754801484616103900195)
                      ·
                        rfl

theorem cell23_3769869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_3769869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769869 prefixEnd_3769869 := by exact prefixLift 3769869
  have htrace : WordTrace (prefixWord ++ tailWord_3769869) baseStart_3769869 baseEnd_3769869 := by
    simpa [prefixWord, tailWord_3769869, baseEnd_3769869] using wordTrace_append hprefix tailTrace_3769869
  have hstable : (prefixWord ++ tailWord_3769869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769869).length < 2 ^ (prefixWord ++ tailWord_3769869).sum := by decide
  have hdescent : baseEnd_3769869 < baseStart_3769869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769887 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 4]
def baseStart_3769887 : Nat := 118140960795 + 3769887 * 2 ^ 59
def prefixEnd_3769887 : Nat := 4983230072969 + 3 ^ 40 * 3769887 * 2
def baseEnd_3769887 : Nat := 1935764044136397033475111

theorem tailTrace_3769887 : CollatzResearch.WordTrace tailWord_3769887 prefixEnd_3769887 1935764044136397033475111 := by
  unfold tailWord_3769887
  simp only [CollatzResearch.WordTrace]
  refine ⟨137499074893350719285555915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91666049928900479523703943 137499074893350719285555915)
  ·
    refine ⟨206248612340026078928333873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137499074893350719285555915 206248612340026078928333873)
    ·
      refine ⟨154686459255019559196250405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206248612340026078928333873 154686459255019559196250405)
      ·
        refine ⟨29003711110316167349296951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154686459255019559196250405 29003711110316167349296951)
        ·
          refine ⟨43505566665474251023945427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29003711110316167349296951 43505566665474251023945427)
          ·
            refine ⟨65258349998211376535918141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43505566665474251023945427 65258349998211376535918141)
            ·
              refine ⟨24471881249329266200969303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65258349998211376535918141 24471881249329266200969303)
              ·
                refine ⟨36707821873993899301453955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24471881249329266200969303 36707821873993899301453955)
                ·
                  refine ⟨55061732810990848952180933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36707821873993899301453955 55061732810990848952180933)
                  ·
                    refine ⟨10324074902060784178533925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55061732810990848952180933 10324074902060784178533925)
                    ·
                      refine ⟨1935764044136397033475111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10324074902060784178533925 1935764044136397033475111)
                      ·
                        rfl

theorem cell23_3769887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_3769887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769887 prefixEnd_3769887 := by exact prefixLift 3769887
  have htrace : WordTrace (prefixWord ++ tailWord_3769887) baseStart_3769887 baseEnd_3769887 := by
    simpa [prefixWord, tailWord_3769887, baseEnd_3769887] using wordTrace_append hprefix tailTrace_3769887
  have hstable : (prefixWord ++ tailWord_3769887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769887).length < 2 ^ (prefixWord ++ tailWord_3769887).sum := by decide
  have hdescent : baseEnd_3769887 < baseStart_3769887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769937 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 1, 1, 7]
def baseStart_3769937 : Nat := 118140960795 + 3769937 * 2 ^ 59
def prefixEnd_3769937 : Nat := 4983230072969 + 3 ^ 40 * 3769937 * 2
def baseEnd_3769937 : Nat := 1935789718169121837849881

theorem tailTrace_3769937 : CollatzResearch.WordTrace tailWord_3769937 prefixEnd_3769937 1935789718169121837849881 := by
  unfold tailWord_3769937
  simp only [CollatzResearch.WordTrace]
  refine ⟨137500898543169577824876065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91667265695446385216584043 137500898543169577824876065)
  ·
    refine ⟨103125673907377183368657049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137500898543169577824876065 103125673907377183368657049)
    ·
      refine ⟨77344255430532887526492787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103125673907377183368657049 77344255430532887526492787)
      ·
        refine ⟨116016383145799331289739181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77344255430532887526492787 116016383145799331289739181)
        ·
          refine ⟨43506143679674749233652193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116016383145799331289739181 43506143679674749233652193)
          ·
            refine ⟨32629607759756061925239145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43506143679674749233652193 32629607759756061925239145)
            ·
              refine ⟨24472205819817046443929359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32629607759756061925239145 24472205819817046443929359)
              ·
                refine ⟨36708308729725569665894039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24472205819817046443929359 36708308729725569665894039)
                ·
                  refine ⟨55062463094588354498841059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36708308729725569665894039 55062463094588354498841059)
                  ·
                    refine ⟨82593694641882531748261589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55062463094588354498841059 82593694641882531748261589)
                    ·
                      refine ⟨1935789718169121837849881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82593694641882531748261589 1935789718169121837849881)
                      ·
                        rfl

theorem cell23_3769937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_3769937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769937 prefixEnd_3769937 := by exact prefixLift 3769937
  have htrace : WordTrace (prefixWord ++ tailWord_3769937) baseStart_3769937 baseEnd_3769937 := by
    simpa [prefixWord, tailWord_3769937, baseEnd_3769937] using wordTrace_append hprefix tailTrace_3769937
  have hstable : (prefixWord ++ tailWord_3769937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769937).length < 2 ^ (prefixWord ++ tailWord_3769937).sum := by decide
  have hdescent : baseEnd_3769937 < baseStart_3769937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769964 : List Nat := [2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 4]
def baseStart_3769964 : Nat := 118140960795 + 3769964 * 2 ^ 59
def prefixEnd_3769964 : Nat := 4983230072969 + 3 ^ 40 * 3769964 * 2
def baseEnd_3769964 : Nat := 1935803582146793232212257

theorem tailTrace_3769964 : CollatzResearch.WordTrace tailWord_3769964 prefixEnd_3769964 1935803582146793232212257 := by
  unfold tailWord_3769964
  simp only [CollatzResearch.WordTrace]
  refine ⟨68750941657035880718054473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91667922209381174290739297 68750941657035880718054473)
  ·
    refine ⟨51563206242776910538540855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68750941657035880718054473 51563206242776910538540855)
    ·
      refine ⟨77344809364165365807811283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51563206242776910538540855 77344809364165365807811283)
      ·
        refine ⟨116017214046248048711716925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77344809364165365807811283 116017214046248048711716925)
        ·
          refine ⟨43506455267343018266893847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116017214046248048711716925 43506455267343018266893847)
          ·
            refine ⟨65259682901014527400340771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43506455267343018266893847 65259682901014527400340771)
            ·
              refine ⟨97889524351521791100511157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65259682901014527400340771 97889524351521791100511157)
              ·
                refine ⟨9177142907955167915672921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97889524351521791100511157 9177142907955167915672921)
                ·
                  refine ⟨6882857180966375936754691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9177142907955167915672921 6882857180966375936754691)
                  ·
                    refine ⟨10324285771449563905132037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6882857180966375936754691 10324285771449563905132037)
                    ·
                      refine ⟨1935803582146793232212257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10324285771449563905132037 1935803582146793232212257)
                      ·
                        rfl

theorem cell23_3769964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_3769964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769964 prefixEnd_3769964 := by exact prefixLift 3769964
  have htrace : WordTrace (prefixWord ++ tailWord_3769964) baseStart_3769964 baseEnd_3769964 := by
    simpa [prefixWord, tailWord_3769964, baseEnd_3769964] using wordTrace_append hprefix tailTrace_3769964
  have hstable : (prefixWord ++ tailWord_3769964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769964).length < 2 ^ (prefixWord ++ tailWord_3769964).sum := by decide
  have hdescent : baseEnd_3769964 < baseStart_3769964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769965 : List Nat := [1, 5, 1, 1, 5, 1, 1, 3, 5]
def baseStart_3769965 : Nat := 118140960795 + 3769965 * 2 ^ 59
def prefixEnd_3769965 : Nat := 4983230072969 + 3 ^ 40 * 3769965 * 2
def baseEnd_3769965 : Nat := 215089343958605303144417

theorem tailTrace_3769965 : CollatzResearch.WordTrace tailWord_3769965 prefixEnd_3769965 215089343958605303144417 := by
  unfold tailWord_3769965
  simp only [CollatzResearch.WordTrace]
  refine ⟨137501919787068138606895349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91667946524712092404596899 137501919787068138606895349)
  ·
    refine ⟨12890804980037637994396439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137501919787068138606895349 12890804980037637994396439)
    ·
      refine ⟨19336207470056456991594659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12890804980037637994396439 19336207470056456991594659)
      ·
        refine ⟨29004311205084685487391989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19336207470056456991594659 29004311205084685487391989)
        ·
          refine ⟨2719154175476689264442999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29004311205084685487391989 2719154175476689264442999)
          ·
            refine ⟨4078731263215033896664499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2719154175476689264442999 4078731263215033896664499)
            ·
              refine ⟨6118096894822550844996749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4078731263215033896664499 6118096894822550844996749)
              ·
                refine ⟨2294286335558456566873781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6118096894822550844996749 2294286335558456566873781)
                ·
                  refine ⟨215089343958605303144417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2294286335558456566873781 215089343958605303144417)
                  ·
                    rfl

theorem cell23_3769965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_3769965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769965 prefixEnd_3769965 := by exact prefixLift 3769965
  have htrace : WordTrace (prefixWord ++ tailWord_3769965) baseStart_3769965 baseEnd_3769965 := by
    simpa [prefixWord, tailWord_3769965, baseEnd_3769965] using wordTrace_append hprefix tailTrace_3769965
  have hstable : (prefixWord ++ tailWord_3769965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769965).length < 2 ^ (prefixWord ++ tailWord_3769965).sum := by decide
  have hdescent : baseEnd_3769965 < baseStart_3769965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769967 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 5]
def baseStart_3769967 : Nat := 118140960795 + 3769967 * 2 ^ 59
def prefixEnd_3769967 : Nat := 4983230072969 + 3 ^ 40 * 3769967 * 2
def baseEnd_3769967 : Nat := 1935805122588756720474743

theorem tailTrace_3769967 : CollatzResearch.WordTrace tailWord_3769967 prefixEnd_3769967 1935805122588756720474743 := by
  unfold tailWord_3769967
  simp only [CollatzResearch.WordTrace]
  refine ⟨137501992733060892948468155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91667995155373928632312103 137501992733060892948468155)
  ·
    refine ⟨206252989099591339422702233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137501992733060892948468155 206252989099591339422702233)
    ·
      refine ⟨154689741824693504567026675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206252989099591339422702233 154689741824693504567026675)
      ·
        refine ⟨232034612737040256850540013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154689741824693504567026675 232034612737040256850540013)
        ·
          refine ⟨87012979776390096318952505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232034612737040256850540013 87012979776390096318952505)
          ·
            refine ⟨65259734832292572239214379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87012979776390096318952505 65259734832292572239214379)
            ·
              refine ⟨97889602248438858358821569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65259734832292572239214379 97889602248438858358821569)
              ·
                refine ⟨73417201686329143769116177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97889602248438858358821569 73417201686329143769116177)
                ·
                  refine ⟨55062901264746857826837133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73417201686329143769116177 55062901264746857826837133)
                  ·
                    refine ⟨20648587974280071685063925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55062901264746857826837133 20648587974280071685063925)
                    ·
                      refine ⟨1935805122588756720474743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20648587974280071685063925 1935805122588756720474743)
                      ·
                        rfl

theorem cell23_3769967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_3769967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769967 prefixEnd_3769967 := by exact prefixLift 3769967
  have htrace : WordTrace (prefixWord ++ tailWord_3769967) baseStart_3769967 baseEnd_3769967 := by
    simpa [prefixWord, tailWord_3769967, baseEnd_3769967] using wordTrace_append hprefix tailTrace_3769967
  have hstable : (prefixWord ++ tailWord_3769967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769967).length < 2 ^ (prefixWord ++ tailWord_3769967).sum := by decide
  have hdescent : baseEnd_3769967 < baseStart_3769967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769981 : List Nat := [1, 4, 1, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_3769981 : Nat := 118140960795 + 3769981 * 2 ^ 59
def prefixEnd_3769981 : Nat := 4983230072969 + 3 ^ 40 * 3769981 * 2
def baseEnd_3769981 : Nat := 1935812311317919665699679

theorem tailTrace_3769981 : CollatzResearch.WordTrace tailWord_3769981 prefixEnd_3769981 1935812311317919665699679 := by
  unfold tailWord_3769981
  simp only [CollatzResearch.WordTrace]
  refine ⟨137502503355010173339477797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91668335570006782226318531 137502503355010173339477797)
  ·
    refine ⟨25781719379064407501152087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137502503355010173339477797 25781719379064407501152087)
    ·
      refine ⟨38672579068596611251728131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25781719379064407501152087 38672579068596611251728131)
      ·
        refine ⟨58008868602894916877592197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38672579068596611251728131 58008868602894916877592197)
        ·
          refine ⟨10876662863042796914548537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58008868602894916877592197 10876662863042796914548537)
          ·
            refine ⟨8157497147282097685911403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10876662863042796914548537 8157497147282097685911403)
            ·
              refine ⟨12236245720923146528867105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8157497147282097685911403 12236245720923146528867105)
              ·
                refine ⟨9177184290692359896650329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12236245720923146528867105 9177184290692359896650329)
                ·
                  refine ⟨6882888218019269922487747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9177184290692359896650329 6882888218019269922487747)
                  ·
                    refine ⟨10324332327028904883731621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6882888218019269922487747 10324332327028904883731621)
                    ·
                      refine ⟨1935812311317919665699679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10324332327028904883731621 1935812311317919665699679)
                      ·
                        rfl

theorem cell23_3769981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_3769981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769981 prefixEnd_3769981 := by exact prefixLift 3769981
  have htrace : WordTrace (prefixWord ++ tailWord_3769981) baseStart_3769981 baseEnd_3769981 := by
    simpa [prefixWord, tailWord_3769981, baseEnd_3769981] using wordTrace_append hprefix tailTrace_3769981
  have hstable : (prefixWord ++ tailWord_3769981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769981).length < 2 ^ (prefixWord ++ tailWord_3769981).sum := by decide
  have hdescent : baseEnd_3769981 < baseStart_3769981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769991 : List Nat := [1, 1, 4, 2, 1, 3, 3, 1, 3, 4]
def baseStart_3769991 : Nat := 118140960795 + 3769991 * 2 ^ 59
def prefixEnd_3769991 : Nat := 4983230072969 + 3 ^ 40 * 3769991 * 2
def baseEnd_3769991 : Nat := 645272482041488208858211

theorem tailTrace_3769991 : CollatzResearch.WordTrace tailWord_3769991 prefixEnd_3769991 645272482041488208858211 := by
  unfold tailWord_3769991
  simp only [CollatzResearch.WordTrace]
  refine ⟨137502868084973945047341827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91668578723315963364894551 137502868084973945047341827)
  ·
    refine ⟨206254302127460917571012741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137502868084973945047341827 206254302127460917571012741)
    ·
      refine ⟨38672681648898922044564889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206254302127460917571012741 38672681648898922044564889)
      ·
        refine ⟨29004511236674191533423667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38672681648898922044564889 29004511236674191533423667)
        ·
          refine ⟨43506766855011287300135501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29004511236674191533423667 43506766855011287300135501)
          ·
            refine ⟨16315037570629232737550813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43506766855011287300135501 16315037570629232737550813)
            ·
              refine ⟨6118139088985962276581555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16315037570629232737550813 6118139088985962276581555)
              ·
                refine ⟨9177208633478943414872333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6118139088985962276581555 9177208633478943414872333)
                ·
                  refine ⟨3441453237554603780577125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9177208633478943414872333 3441453237554603780577125)
                  ·
                    refine ⟨645272482041488208858211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3441453237554603780577125 645272482041488208858211)
                    ·
                      rfl

theorem cell23_3769991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_3769991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3769991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3769991 prefixEnd_3769991 := by exact prefixLift 3769991
  have htrace : WordTrace (prefixWord ++ tailWord_3769991) baseStart_3769991 baseEnd_3769991 := by
    simpa [prefixWord, tailWord_3769991, baseEnd_3769991] using wordTrace_append hprefix tailTrace_3769991
  have hstable : (prefixWord ++ tailWord_3769991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769991).length < 2 ^ (prefixWord ++ tailWord_3769991).sum := by decide
  have hdescent : baseEnd_3769991 < baseStart_3769991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770038 : List Nat := [5, 1, 3, 1, 1, 1, 1, 4, 6]
def baseStart_3770038 : Nat := 118140960795 + 3770038 * 2 ^ 59
def prefixEnd_3770038 : Nat := 4983230072969 + 3 ^ 40 * 3770038 * 2
def baseEnd_3770038 : Nat := 215093508857247326965213

theorem tailTrace_3770038 : CollatzResearch.WordTrace tailWord_3770038 prefixEnd_3770038 215093508857247326965213 := by
  unfold tailWord_3770038
  simp only [CollatzResearch.WordTrace]
  refine ⟨8594036394737729504643923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91669721543869114716201845 8594036394737729504643923)
  ·
    refine ⟨12891054592106594256965885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8594036394737729504643923 12891054592106594256965885)
    ·
      refine ⟨4834145472039972846362207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12891054592106594256965885 4834145472039972846362207)
      ·
        refine ⟨7251218208059959269543311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4834145472039972846362207 7251218208059959269543311)
        ·
          refine ⟨10876827312089938904314967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7251218208059959269543311 10876827312089938904314967)
          ·
            refine ⟨16315240968134908356472451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10876827312089938904314967 16315240968134908356472451)
            ·
              refine ⟨24472861452202362534708677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16315240968134908356472451 24472861452202362534708677)
              ·
                refine ⟨4588661522287942975257877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24472861452202362534708677 4588661522287942975257877)
                ·
                  refine ⟨215093508857247326965213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4588661522287942975257877 215093508857247326965213)
                  ·
                    rfl

theorem cell23_3770038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_3770038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770038 prefixEnd_3770038 := by exact prefixLift 3770038
  have htrace : WordTrace (prefixWord ++ tailWord_3770038) baseStart_3770038 baseEnd_3770038 := by
    simpa [prefixWord, tailWord_3770038, baseEnd_3770038] using wordTrace_append hprefix tailTrace_3770038
  have hstable : (prefixWord ++ tailWord_3770038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770038).length < 2 ^ (prefixWord ++ tailWord_3770038).sum := by decide
  have hdescent : baseEnd_3770038 < baseStart_3770038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770071 : List Nat := [1, 1, 3, 2, 1, 3, 2, 4, 1, 1, 4]
def baseStart_3770071 : Nat := 118140960795 + 3770071 * 2 ^ 59
def prefixEnd_3770071 : Nat := 4983230072969 + 3 ^ 40 * 3770071 * 2
def baseEnd_3770071 : Nat := 1935858524576824313574265

theorem tailTrace_3770071 : CollatzResearch.WordTrace tailWord_3770071 prefixEnd_3770071 1935858524576824313574265 := by
  unfold tailWord_3770071
  simp only [CollatzResearch.WordTrace]
  refine ⟨137505785924684118710254067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91670523949789412473502711 137505785924684118710254067)
  ·
    refine ⟨206258678887026178065381101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137505785924684118710254067 206258678887026178065381101)
    ·
      refine ⟨77347004582634816774517913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206258678887026178065381101 77347004582634816774517913)
      ·
        refine ⟨58010253436976112580888435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77347004582634816774517913 58010253436976112580888435)
        ·
          refine ⟨87015380155464168871332653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58010253436976112580888435 87015380155464168871332653)
          ·
            refine ⟨32630767558299063326749745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87015380155464168871332653 32630767558299063326749745)
            ·
              refine ⟨24473075668724297495062309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32630767558299063326749745 24473075668724297495062309)
              ·
                refine ⟨4588701687885805780324183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24473075668724297495062309 4588701687885805780324183)
                ·
                  refine ⟨6883052531828708670486275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4588701687885805780324183 6883052531828708670486275)
                  ·
                    refine ⟨10324578797743063005729413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6883052531828708670486275 10324578797743063005729413)
                    ·
                      refine ⟨1935858524576824313574265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10324578797743063005729413 1935858524576824313574265)
                      ·
                        rfl

theorem cell23_3770071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_3770071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770071 prefixEnd_3770071 := by exact prefixLift 3770071
  have htrace : WordTrace (prefixWord ++ tailWord_3770071) baseStart_3770071 baseEnd_3770071 := by
    simpa [prefixWord, tailWord_3770071, baseEnd_3770071] using wordTrace_append hprefix tailTrace_3770071
  have hstable : (prefixWord ++ tailWord_3770071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770071).length < 2 ^ (prefixWord ++ tailWord_3770071).sum := by decide
  have hdescent : baseEnd_3770071 < baseStart_3770071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770088 : List Nat := [2, 1, 4, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_3770088 : Nat := 118140960795 + 3770088 * 2 ^ 59
def prefixEnd_3770088 : Nat := 4983230072969 + 3 ^ 40 * 3770088 * 2
def baseEnd_3770088 : Nat := 1935867253747950747061687

theorem tailTrace_3770088 : CollatzResearch.WordTrace tailWord_3770088 prefixEnd_3770088 1935867253747950747061687 := by
  unfold tailWord_3770088
  simp only [CollatzResearch.WordTrace]
  refine ⟨68753202982811265306811459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91670937310415020409081945 68753202982811265306811459)
  ·
    refine ⟨103129804474216897960217189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68753202982811265306811459 103129804474216897960217189)
    ·
      refine ⟨19336838338915668367540723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103129804474216897960217189 19336838338915668367540723)
      ·
        refine ⟨29005257508373502551311085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19336838338915668367540723 29005257508373502551311085)
        ·
          refine ⟨10876971565640063456741657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29005257508373502551311085 10876971565640063456741657)
          ·
            refine ⟨8157728674230047592556243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10876971565640063456741657 8157728674230047592556243)
            ·
              refine ⟨12236593011345071388834365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8157728674230047592556243 12236593011345071388834365)
              ·
                refine ⟨4588722379254401770812887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12236593011345071388834365 4588722379254401770812887)
                ·
                  refine ⟨6883083568881602656219331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4588722379254401770812887 6883083568881602656219331)
                  ·
                    refine ⟨10324625353322403984328997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6883083568881602656219331 10324625353322403984328997)
                    ·
                      refine ⟨1935867253747950747061687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10324625353322403984328997 1935867253747950747061687)
                      ·
                        rfl

theorem cell23_3770088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_3770088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770088 prefixEnd_3770088 := by exact prefixLift 3770088
  have htrace : WordTrace (prefixWord ++ tailWord_3770088) baseStart_3770088 baseEnd_3770088 := by
    simpa [prefixWord, tailWord_3770088, baseEnd_3770088] using wordTrace_append hprefix tailTrace_3770088
  have hstable : (prefixWord ++ tailWord_3770088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770088).length < 2 ^ (prefixWord ++ tailWord_3770088).sum := by decide
  have hdescent : baseEnd_3770088 < baseStart_3770088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770094 : List Nat := [4, 1, 2, 1, 1, 2, 12]
def baseStart_3770094 : Nat := 118140960795 + 3770094 * 2 ^ 59
def prefixEnd_3770094 : Nat := 4983230072969 + 3 ^ 40 * 3770094 * 2
def baseEnd_3770094 : Nat := 23899633760887379303539

theorem tailTrace_3770094 : CollatzResearch.WordTrace tailWord_3770094 prefixEnd_3770094 23899633760887379303539 := by
  unfold tailWord_3770094
  simp only [CollatzResearch.WordTrace]
  refine ⟨17188328100450099204792667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91671083202400529092227557 17188328100450099204792667)
  ·
    refine ⟨25782492150675148807189001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17188328100450099204792667 25782492150675148807189001)
    ·
      refine ⟨19336869113006361605391751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25782492150675148807189001 19336869113006361605391751)
      ·
        refine ⟨29005303669509542408087627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19336869113006361605391751 29005303669509542408087627)
        ·
          refine ⟨43507955504264313612131441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29005303669509542408087627 43507955504264313612131441)
          ·
            refine ⟨32630966628198235209098581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43507955504264313612131441 32630966628198235209098581)
            ·
              refine ⟨23899633760887379303539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 32630966628198235209098581 23899633760887379303539)
              ·
                rfl

theorem cell23_3770094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 12].length) (baseStart_3770094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770094 prefixEnd_3770094 := by exact prefixLift 3770094
  have htrace : WordTrace (prefixWord ++ tailWord_3770094) baseStart_3770094 baseEnd_3770094 := by
    simpa [prefixWord, tailWord_3770094, baseEnd_3770094] using wordTrace_append hprefix tailTrace_3770094
  have hstable : (prefixWord ++ tailWord_3770094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770094).length < 2 ^ (prefixWord ++ tailWord_3770094).sum := by decide
  have hdescent : baseEnd_3770094 < baseStart_3770094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770124 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 2, 7]
def baseStart_3770124 : Nat := 118140960795 + 3770124 * 2 ^ 59
def prefixEnd_3770124 : Nat := 4983230072969 + 3 ^ 40 * 3770124 * 2
def baseEnd_3770124 : Nat := 645295246350504202070507

theorem tailTrace_3770124 : CollatzResearch.WordTrace tailWord_3770124 prefixEnd_3770124 645295246350504202070507 := by
  unfold tailWord_3770124
  simp only [CollatzResearch.WordTrace]
  refine ⟨68753859496746054380966713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91671812662328072507955617 68753859496746054380966713)
  ·
    refine ⟨51565394622559540785725035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68753859496746054380966713 51565394622559540785725035)
    ·
      refine ⟨77348091933839311178587553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51565394622559540785725035 77348091933839311178587553)
      ·
        refine ⟨58011068950379483383940665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77348091933839311178587553 58011068950379483383940665)
        ·
          refine ⟨43508301712784612537955499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58011068950379483383940665 43508301712784612537955499)
          ·
            refine ⟨65262452569176918806933249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43508301712784612537955499 65262452569176918806933249)
            ·
              refine ⟨48946839426882689105199937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65262452569176918806933249 48946839426882689105199937)
              ·
                refine ⟨36710129570162016828899953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48946839426882689105199937 36710129570162016828899953)
                ·
                  refine ⟨27532597177621512621674965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36710129570162016828899953 27532597177621512621674965)
                  ·
                    refine ⟨645295246350504202070507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27532597177621512621674965 645295246350504202070507)
                    ·
                      rfl

theorem cell23_3770124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_3770124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770124 prefixEnd_3770124 := by exact prefixLift 3770124
  have htrace : WordTrace (prefixWord ++ tailWord_3770124) baseStart_3770124 baseEnd_3770124 := by
    simpa [prefixWord, tailWord_3770124, baseEnd_3770124] using wordTrace_append hprefix tailTrace_3770124
  have hstable : (prefixWord ++ tailWord_3770124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770124).length < 2 ^ (prefixWord ++ tailWord_3770124).sum := by decide
  have hdescent : baseEnd_3770124 < baseStart_3770124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770138 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3]
def baseStart_3770138 : Nat := 118140960795 + 3770138 * 2 ^ 59
def prefixEnd_3770138 : Nat := 4983230072969 + 3 ^ 40 * 3770138 * 2
def baseEnd_3770138 : Nat := 1935892927780675551436457

theorem tailTrace_3770138 : CollatzResearch.WordTrace tailWord_3770138 prefixEnd_3770138 1935892927780675551436457 := by
  unfold tailWord_3770138
  simp only [CollatzResearch.WordTrace]
  refine ⟨34377057403860347288235767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91672153076960926101962045 34377057403860347288235767)
  ·
    refine ⟨51565586105790520932353651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34377057403860347288235767 51565586105790520932353651)
    ·
      refine ⟨77348379158685781398530477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51565586105790520932353651 77348379158685781398530477)
      ·
        refine ⟨29005642184507168024448929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77348379158685781398530477 29005642184507168024448929)
        ·
          refine ⟨21754231638380376018336697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29005642184507168024448929 21754231638380376018336697)
          ·
            refine ⟨16315673728785282013752523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21754231638380376018336697 16315673728785282013752523)
            ·
              refine ⟨24473510593177923020628785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16315673728785282013752523 24473510593177923020628785)
              ·
                refine ⟨18355132944883442265471589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24473510593177923020628785 18355132944883442265471589)
                ·
                  refine ⟨3441587427165645424775923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18355132944883442265471589 3441587427165645424775923)
                  ·
                    refine ⟨5162381140748468137163885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3441587427165645424775923 5162381140748468137163885)
                    ·
                      refine ⟨1935892927780675551436457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5162381140748468137163885 1935892927780675551436457)
                      ·
                        rfl

theorem cell23_3770138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_3770138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770138 prefixEnd_3770138 := by exact prefixLift 3770138
  have htrace : WordTrace (prefixWord ++ tailWord_3770138) baseStart_3770138 baseEnd_3770138 := by
    simpa [prefixWord, tailWord_3770138, baseEnd_3770138] using wordTrace_append hprefix tailTrace_3770138
  have hstable : (prefixWord ++ tailWord_3770138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770138).length < 2 ^ (prefixWord ++ tailWord_3770138).sum := by decide
  have hdescent : baseEnd_3770138 < baseStart_3770138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770142 : List Nat := [4, 3, 2, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_3770142 : Nat := 118140960795 + 3770142 * 2 ^ 59
def prefixEnd_3770142 : Nat := 4983230072969 + 3 ^ 40 * 3770142 * 2
def baseEnd_3770142 : Nat := 1935894981703293535786439

theorem tailTrace_3770142 : CollatzResearch.WordTrace tailWord_3770142 prefixEnd_3770142 1935894981703293535786439 := by
  unfold tailWord_3770142
  simp only [CollatzResearch.WordTrace]
  refine ⟨17188546938428362229511085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91672250338284598557392453 17188546938428362229511085)
  ·
    refine ⟨6445705101910635836066657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17188546938428362229511085 6445705101910635836066657)
    ·
      refine ⟨4834278826432976877049993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6445705101910635836066657 4834278826432976877049993)
      ·
        refine ⟨3625709119824732657787495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4834278826432976877049993 3625709119824732657787495)
        ·
          refine ⟨5438563679737098986681243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3625709119824732657787495 5438563679737098986681243)
          ·
            refine ⟨8157845519605648480021865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5438563679737098986681243 8157845519605648480021865)
            ·
              refine ⟨6118384139704236360016399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8157845519605648480021865 6118384139704236360016399)
              ·
                refine ⟨9177576209556354540024599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6118384139704236360016399 9177576209556354540024599)
                ·
                  refine ⟨13766364314334531810036899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9177576209556354540024599 13766364314334531810036899)
                  ·
                    refine ⟨20649546471501797715055349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13766364314334531810036899 20649546471501797715055349)
                    ·
                      refine ⟨1935894981703293535786439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20649546471501797715055349 1935894981703293535786439)
                      ·
                        rfl

theorem cell23_3770142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_3770142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770142 prefixEnd_3770142 := by exact prefixLift 3770142
  have htrace : WordTrace (prefixWord ++ tailWord_3770142) baseStart_3770142 baseEnd_3770142 := by
    simpa [prefixWord, tailWord_3770142, baseEnd_3770142] using wordTrace_append hprefix tailTrace_3770142
  have hstable : (prefixWord ++ tailWord_3770142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770142).length < 2 ^ (prefixWord ++ tailWord_3770142).sum := by decide
  have hdescent : baseEnd_3770142 < baseStart_3770142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770248 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 1, 7]
def baseStart_3770248 : Nat := 118140960795 + 3770248 * 2 ^ 59
def prefixEnd_3770248 : Nat := 4983230072969 + 3 ^ 40 * 3770248 * 2
def baseEnd_3770248 : Nat := 645316470217556707020317

theorem tailTrace_3770248 : CollatzResearch.WordTrace tailWord_3770248 prefixEnd_3770248 645316470217556707020317 := by
  unfold tailWord_3770248
  simp only [CollatzResearch.WordTrace]
  refine ⟨68756120822521438969723699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91674827763361918626298265 68756120822521438969723699)
  ·
    refine ⟨103134181233782158454585549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68756120822521438969723699 103134181233782158454585549)
    ·
      refine ⟨38675317962668309420469581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103134181233782158454585549 38675317962668309420469581)
      ·
        refine ⟨14503244236000616032676093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38675317962668309420469581 14503244236000616032676093)
        ·
          refine ⟨5438716588500231012253535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14503244236000616032676093 5438716588500231012253535)
          ·
            refine ⟨8158074882750346518380303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5438716588500231012253535 8158074882750346518380303)
            ·
              refine ⟨12237112324125519777570455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8158074882750346518380303 12237112324125519777570455)
              ·
                refine ⟨18355668486188279666355683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12237112324125519777570455 18355668486188279666355683)
                ·
                  refine ⟨27533502729282419499533525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18355668486188279666355683 27533502729282419499533525)
                  ·
                    refine ⟨645316470217556707020317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27533502729282419499533525 645316470217556707020317)
                    ·
                      rfl

theorem cell23_3770248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_3770248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770248 prefixEnd_3770248 := by exact prefixLift 3770248
  have htrace : WordTrace (prefixWord ++ tailWord_3770248) baseStart_3770248 baseEnd_3770248 := by
    simpa [prefixWord, tailWord_3770248, baseEnd_3770248] using wordTrace_append hprefix tailTrace_3770248
  have hstable : (prefixWord ++ tailWord_3770248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770248).length < 2 ^ (prefixWord ++ tailWord_3770248).sum := by decide
  have hdescent : baseEnd_3770248 < baseStart_3770248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770312 : List Nat := [2, 1, 3, 1, 4, 1, 3, 3, 1, 4]
def baseStart_3770312 : Nat := 118140960795 + 3770312 * 2 ^ 59
def prefixEnd_3770312 : Nat := 4983230072969 + 3 ^ 40 * 3770312 * 2
def baseEnd_3770312 : Nat := 645327424471519290220219

theorem tailTrace_3770312 : CollatzResearch.WordTrace tailWord_3770312 prefixEnd_3770312 645327424471519290220219 := by
  unfold tailWord_3770312
  simp only [CollatzResearch.WordTrace]
  refine ⟨68757287958405508434888595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91676383944540677913184793 68757287958405508434888595)
  ·
    refine ⟨103135931937608262652332893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68757287958405508434888595 103135931937608262652332893)
    ·
      refine ⟨38675974476603098494624835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103135931937608262652332893 38675974476603098494624835)
      ·
        refine ⟨58013961714904647741937253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38675974476603098494624835 58013961714904647741937253)
        ·
          refine ⟨10877617821544621451613235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58013961714904647741937253 10877617821544621451613235)
          ·
            refine ⟨16316426732316932177419853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10877617821544621451613235 16316426732316932177419853)
            ·
              refine ⟨6118660024618849566532445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16316426732316932177419853 6118660024618849566532445)
              ·
                refine ⟨2294497509232068587449667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6118660024618849566532445 2294497509232068587449667)
                ·
                  refine ⟨3441746263848102881174501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2294497509232068587449667 3441746263848102881174501)
                  ·
                    refine ⟨645327424471519290220219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3441746263848102881174501 645327424471519290220219)
                    ·
                      rfl

theorem cell23_3770312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_3770312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770312 prefixEnd_3770312 := by exact prefixLift 3770312
  have htrace : WordTrace (prefixWord ++ tailWord_3770312) baseStart_3770312 baseEnd_3770312 := by
    simpa [prefixWord, tailWord_3770312, baseEnd_3770312] using wordTrace_append hprefix tailTrace_3770312
  have hstable : (prefixWord ++ tailWord_3770312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770312).length < 2 ^ (prefixWord ++ tailWord_3770312).sum := by decide
  have hdescent : baseEnd_3770312 < baseStart_3770312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770322 : List Nat := [3, 2, 2, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_3770322 : Nat := 118140960795 + 3770322 * 2 ^ 59
def prefixEnd_3770322 : Nat := 4983230072969 + 3 ^ 40 * 3770322 * 2
def baseEnd_3770322 : Nat := 1935987408221102831535611

theorem tailTrace_3770322 : CollatzResearch.WordTrace tailWord_3770322 prefixEnd_3770322 1935987408221102831535611 := by
  unfold tailWord_3770322
  simp only [CollatzResearch.WordTrace]
  refine ⟨34378735161693697144410305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91676627097849859051760813 34378735161693697144410305)
  ·
    refine ⟨25784051371270272858307729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34378735161693697144410305 25784051371270272858307729)
    ·
      refine ⟨19338038528452704643730797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25784051371270272858307729 19338038528452704643730797)
      ·
        refine ⟨7251764448169764241399049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19338038528452704643730797 7251764448169764241399049)
        ·
          refine ⟨5438823336127323181049287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7251764448169764241399049 5438823336127323181049287)
          ·
            refine ⟨8158235004190984771573931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5438823336127323181049287 8158235004190984771573931)
            ·
              refine ⟨12237352506286477157360897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8158235004190984771573931 12237352506286477157360897)
              ·
                refine ⟨9178014379714857868020673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12237352506286477157360897 9178014379714857868020673)
                ·
                  refine ⟨6883510784786143401015505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9178014379714857868020673 6883510784786143401015505)
                  ·
                    refine ⟨5162633088589607550761629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6883510784786143401015505 5162633088589607550761629)
                    ·
                      refine ⟨1935987408221102831535611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5162633088589607550761629 1935987408221102831535611)
                      ·
                        rfl

theorem cell23_3770322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_3770322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770322 prefixEnd_3770322 := by exact prefixLift 3770322
  have htrace : WordTrace (prefixWord ++ tailWord_3770322) baseStart_3770322 baseEnd_3770322 := by
    simpa [prefixWord, tailWord_3770322, baseEnd_3770322] using wordTrace_append hprefix tailTrace_3770322
  have hstable : (prefixWord ++ tailWord_3770322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770322).length < 2 ^ (prefixWord ++ tailWord_3770322).sum := by decide
  have hdescent : baseEnd_3770322 < baseStart_3770322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770329 : List Nat := [1, 2, 1, 2, 6, 1, 3, 2, 1, 4]
def baseStart_3770329 : Nat := 118140960795 + 3770329 * 2 ^ 59
def prefixEnd_3770329 : Nat := 4983230072969 + 3 ^ 40 * 3770329 * 2
def baseEnd_3770329 : Nat := 645330334195228101382693

theorem tailTrace_3770329 : CollatzResearch.WordTrace tailWord_3770329 prefixEnd_3770329 645330334195228101382693 := by
  unfold tailWord_3770329
  simp only [CollatzResearch.WordTrace]
  refine ⟨137515195957749428773146041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91676797305166285848764027 137515195957749428773146041)
  ·
    refine ⟨103136396968312071579859531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137515195957749428773146041 103136396968312071579859531)
    ·
      refine ⟨154704595452468107369789297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103136396968312071579859531 154704595452468107369789297)
      ·
        refine ⟨116028446589351080527341973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154704595452468107369789297 116028446589351080527341973)
        ·
          refine ⟨5438833433875831899719155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 116028446589351080527341973 5438833433875831899719155)
          ·
            refine ⟨8158250150813747849578733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5438833433875831899719155 8158250150813747849578733)
            ·
              refine ⟨3059343806555155443592025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8158250150813747849578733 3059343806555155443592025)
              ·
                refine ⟨2294507854916366582694019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3059343806555155443592025 2294507854916366582694019)
                ·
                  refine ⟨3441761782374549874041029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2294507854916366582694019 3441761782374549874041029)
                  ·
                    refine ⟨645330334195228101382693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3441761782374549874041029 645330334195228101382693)
                    ·
                      rfl

theorem cell23_3770329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 1, 4].length) (baseStart_3770329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770329 prefixEnd_3770329 := by exact prefixLift 3770329
  have htrace : WordTrace (prefixWord ++ tailWord_3770329) baseStart_3770329 baseEnd_3770329 := by
    simpa [prefixWord, tailWord_3770329, baseEnd_3770329] using wordTrace_append hprefix tailTrace_3770329
  have hstable : (prefixWord ++ tailWord_3770329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770329).length < 2 ^ (prefixWord ++ tailWord_3770329).sum := by decide
  have hdescent : baseEnd_3770329 < baseStart_3770329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770368 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 4, 4]
def baseStart_3770368 : Nat := 118140960795 + 3770368 * 2 ^ 59
def prefixEnd_3770368 : Nat := 4983230072969 + 3 ^ 40 * 3770368 * 2
def baseEnd_3770368 : Nat := 645337009443736550520133

theorem tailTrace_3770368 : CollatzResearch.WordTrace tailWord_3770368 prefixEnd_3770368 645337009443736550520133 := by
  unfold tailWord_3770368
  simp only [CollatzResearch.WordTrace]
  refine ⟨68758309202304069216907879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91677745603072092289210505 68758309202304069216907879)
  ·
    refine ⟨103137463803456103825361819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68758309202304069216907879 103137463803456103825361819)
    ·
      refine ⟨154706195705184155738042729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103137463803456103825361819 154706195705184155738042729)
      ·
        refine ⟨116029646778888116803532047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154706195705184155738042729 116029646778888116803532047)
        ·
          refine ⟨174044470168332175205298071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116029646778888116803532047 174044470168332175205298071)
          ·
            refine ⟨261066705252498262807947107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174044470168332175205298071 261066705252498262807947107)
            ·
              refine ⟨391600057878747394211920661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261066705252498262807947107 391600057878747394211920661)
              ·
                refine ⟨18356252713066284103683781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 391600057878747394211920661 18356252713066284103683781)
                ·
                  refine ⟨3441797383699928269440709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18356252713066284103683781 3441797383699928269440709)
                  ·
                    refine ⟨645337009443736550520133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3441797383699928269440709 645337009443736550520133)
                    ·
                      rfl

theorem cell23_3770368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 4, 4].length) (baseStart_3770368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770368 prefixEnd_3770368 := by exact prefixLift 3770368
  have htrace : WordTrace (prefixWord ++ tailWord_3770368) baseStart_3770368 baseEnd_3770368 := by
    simpa [prefixWord, tailWord_3770368, baseEnd_3770368] using wordTrace_append hprefix tailTrace_3770368
  have hstable : (prefixWord ++ tailWord_3770368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770368).length < 2 ^ (prefixWord ++ tailWord_3770368).sum := by decide
  have hdescent : baseEnd_3770368 < baseStart_3770368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770392 : List Nat := [2, 1, 2, 3, 2, 1, 2, 3, 3, 2, 2]
def baseStart_3770392 : Nat := 118140960795 + 3770392 * 2 ^ 59
def prefixEnd_3770392 : Nat := 4983230072969 + 3 ^ 40 * 3770392 * 2
def baseEnd_3770392 : Nat := 1936023351866917557660289

theorem tailTrace_3770392 : CollatzResearch.WordTrace tailWord_3770392 prefixEnd_3770392 1936023351866917557660289 := by
  unfold tailWord_3770392
  simp only [CollatzResearch.WordTrace]
  refine ⟨68758746878260595266344715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91678329171014127021792953 68758746878260595266344715)
  ·
    refine ⟨103138120317390892899517073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68758746878260595266344715 103138120317390892899517073)
    ·
      refine ⟨77353590238043169674637805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103138120317390892899517073 77353590238043169674637805)
      ·
        refine ⟨29007596339266188627989177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77353590238043169674637805 29007596339266188627989177)
        ·
          refine ⟨21755697254449641470991883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29007596339266188627989177 21755697254449641470991883)
          ·
            refine ⟨32633545881674462206487825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21755697254449641470991883 32633545881674462206487825)
            ·
              refine ⟨24475159411255846654865869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32633545881674462206487825 24475159411255846654865869)
              ·
                refine ⟨9178184779220942495574701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24475159411255846654865869 9178184779220942495574701)
                ·
                  refine ⟨3441819292207853435840513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9178184779220942495574701 3441819292207853435840513)
                  ·
                    refine ⟨2581364469155890076880385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3441819292207853435840513 2581364469155890076880385)
                    ·
                      refine ⟨1936023351866917557660289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2581364469155890076880385 1936023351866917557660289)
                      ·
                        rfl

theorem cell23_3770392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_3770392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770392 prefixEnd_3770392 := by exact prefixLift 3770392
  have htrace : WordTrace (prefixWord ++ tailWord_3770392) baseStart_3770392 baseEnd_3770392 := by
    simpa [prefixWord, tailWord_3770392, baseEnd_3770392] using wordTrace_append hprefix tailTrace_3770392
  have hstable : (prefixWord ++ tailWord_3770392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770392).length < 2 ^ (prefixWord ++ tailWord_3770392).sum := by decide
  have hdescent : baseEnd_3770392 < baseStart_3770392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770405 : List Nat := [1, 3, 1, 2, 2, 4, 2, 1, 1, 2, 4]
def baseStart_3770405 : Nat := 118140960795 + 3770405 * 2 ^ 59
def prefixEnd_3770405 : Nat := 4983230072969 + 3 ^ 40 * 3770405 * 2
def baseEnd_3770405 : Nat := 1936030027115426006797729

theorem tailTrace_3770405 : CollatzResearch.WordTrace tailWord_3770405 prefixEnd_3770405 1936030027115426006797729 := by
  unfold tailWord_3770405
  simp only [CollatzResearch.WordTrace]
  refine ⟨137517967905474093752912669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91678645270316062501941779 137517967905474093752912669)
  ·
    refine ⟨51569237964552785157342251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137517967905474093752912669 51569237964552785157342251)
    ·
      refine ⟨77353856946829177736013377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51569237964552785157342251 77353856946829177736013377)
      ·
        refine ⟨58015392710121883302010033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77353856946829177736013377 58015392710121883302010033)
        ·
          refine ⟨43511544532591412476507525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58015392710121883302010033 43511544532591412476507525)
          ·
            refine ⟨8158414599860889839345161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43511544532591412476507525 8158414599860889839345161)
            ·
              refine ⟨6118810949895667379508871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8158414599860889839345161 6118810949895667379508871)
              ·
                refine ⟨9178216424843501069263307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6118810949895667379508871 9178216424843501069263307)
                ·
                  refine ⟨13767324637265251603894961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9178216424843501069263307 13767324637265251603894961)
                  ·
                    refine ⟨10325493477948938702921221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13767324637265251603894961 10325493477948938702921221)
                    ·
                      refine ⟨1936030027115426006797729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10325493477948938702921221 1936030027115426006797729)
                      ·
                        rfl

theorem cell23_3770405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_3770405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770405 prefixEnd_3770405 := by exact prefixLift 3770405
  have htrace : WordTrace (prefixWord ++ tailWord_3770405) baseStart_3770405 baseEnd_3770405 := by
    simpa [prefixWord, tailWord_3770405, baseEnd_3770405] using wordTrace_append hprefix tailTrace_3770405
  have hstable : (prefixWord ++ tailWord_3770405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770405).length < 2 ^ (prefixWord ++ tailWord_3770405).sum := by decide
  have hdescent : baseEnd_3770405 < baseStart_3770405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770435 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 5, 3, 2]
def baseStart_3770435 : Nat := 118140960795 + 3770435 * 2 ^ 59
def prefixEnd_3770435 : Nat := 4983230072969 + 3 ^ 40 * 3770435 * 2
def baseEnd_3770435 : Nat := 1936045431535060889422591

theorem tailTrace_3770435 : CollatzResearch.WordTrace tailWord_3770435 prefixEnd_3770435 1936045431535060889422591 := by
  unfold tailWord_3770435
  simp only [CollatzResearch.WordTrace]
  refine ⟨137519062095365408876504759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91679374730243605917669839 137519062095365408876504759)
  ·
    refine ⟨206278593143048113314757139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137519062095365408876504759 206278593143048113314757139)
    ·
      refine ⟨309417889714572169972135709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206278593143048113314757139 309417889714572169972135709)
      ·
        refine ⟨116031708642964563739550891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309417889714572169972135709 116031708642964563739550891)
        ·
          refine ⟨174047562964446845609326337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116031708642964563739550891 174047562964446845609326337)
          ·
            refine ⟨130535672223335134206994753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174047562964446845609326337 130535672223335134206994753)
            ·
              refine ⟨97901754167501350655246065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130535672223335134206994753 97901754167501350655246065)
              ·
                refine ⟨73426315625626012991434549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97901754167501350655246065 73426315625626012991434549)
                ·
                  refine ⟨6883717089902438717946989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73426315625626012991434549 6883717089902438717946989)
                  ·
                    refine ⟨2581393908713414519230121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6883717089902438717946989 2581393908713414519230121)
                    ·
                      refine ⟨1936045431535060889422591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2581393908713414519230121 1936045431535060889422591)
                      ·
                        rfl

theorem cell23_3770435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 3, 2].length) (baseStart_3770435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770435 prefixEnd_3770435 := by exact prefixLift 3770435
  have htrace : WordTrace (prefixWord ++ tailWord_3770435) baseStart_3770435 baseEnd_3770435 := by
    simpa [prefixWord, tailWord_3770435, baseEnd_3770435] using wordTrace_append hprefix tailTrace_3770435
  have hstable : (prefixWord ++ tailWord_3770435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770435).length < 2 ^ (prefixWord ++ tailWord_3770435).sum := by decide
  have hdescent : baseEnd_3770435 < baseStart_3770435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770458 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 2, 6]
def baseStart_3770458 : Nat := 118140960795 + 3770458 * 2 ^ 59
def prefixEnd_3770458 : Nat := 4983230072969 + 3 ^ 40 * 3770458 * 2
def baseEnd_3770458 : Nat := 645352413863371433144995

theorem tailTrace_3770458 : CollatzResearch.WordTrace tailWord_3770458 prefixEnd_3770458 645352413863371433144995 := by
  unfold tailWord_3770458
  simp only [CollatzResearch.WordTrace]
  refine ⟨34379975243570520951148007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91679933982854722536394685 34379975243570520951148007)
  ·
    refine ⟨51569962865355781426722011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34379975243570520951148007 51569962865355781426722011)
    ·
      refine ⟨77354944298033672140083017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51569962865355781426722011 77354944298033672140083017)
      ·
        refine ⟨58016208223525254105062263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77354944298033672140083017 58016208223525254105062263)
        ·
          refine ⟨87024312335287881157593395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58016208223525254105062263 87024312335287881157593395)
          ·
            refine ⟨130536468502931821736390093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87024312335287881157593395 130536468502931821736390093)
            ·
              refine ⟨48951175688599433151146285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130536468502931821736390093 48951175688599433151146285)
              ·
                refine ⟨18356690883224787431679857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48951175688599433151146285 18356690883224787431679857)
                ·
                  refine ⟨13767518162418590573759893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18356690883224787431679857 13767518162418590573759893)
                  ·
                    refine ⟨645352413863371433144995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13767518162418590573759893 645352413863371433144995)
                    ·
                      rfl

theorem cell23_3770458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_3770458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770458 prefixEnd_3770458 := by exact prefixLift 3770458
  have htrace : WordTrace (prefixWord ++ tailWord_3770458) baseStart_3770458 baseEnd_3770458 := by
    simpa [prefixWord, tailWord_3770458, baseEnd_3770458] using wordTrace_append hprefix tailTrace_3770458
  have hstable : (prefixWord ++ tailWord_3770458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770458).length < 2 ^ (prefixWord ++ tailWord_3770458).sum := by decide
  have hdescent : baseEnd_3770458 < baseStart_3770458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770469 : List Nat := [1, 3, 1, 3, 2, 3, 2, 2, 1, 3, 2]
def baseStart_3770469 : Nat := 118140960795 + 3770469 * 2 ^ 59
def prefixEnd_3770469 : Nat := 4983230072969 + 3 ^ 40 * 3770469 * 2
def baseEnd_3770469 : Nat := 1936062889877313756397435

theorem tailTrace_3770469 : CollatzResearch.WordTrace tailWord_3770469 prefixEnd_3770469 1936062889877313756397435 := by
  unfold tailWord_3770469
  simp only [CollatzResearch.WordTrace]
  refine ⟨137520302177242232683242461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91680201451494821788828307 137520302177242232683242461)
  ·
    refine ⟨51570113316465837256215923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137520302177242232683242461 51570113316465837256215923)
    ·
      refine ⟨77355169974698755884323885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51570113316465837256215923 77355169974698755884323885)
      ·
        refine ⟨29008188740512033456621457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77355169974698755884323885 29008188740512033456621457)
        ·
          refine ⟨21756141555384025092466093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29008188740512033456621457 21756141555384025092466093)
          ·
            refine ⟨8158553083269009409674785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21756141555384025092466093 8158553083269009409674785)
            ·
              refine ⟨6118914812451757057256089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8158553083269009409674785 6118914812451757057256089)
              ·
                refine ⟨4589186109338817792942067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6118914812451757057256089 4589186109338817792942067)
                ·
                  refine ⟨6883779164008226689413101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4589186109338817792942067 6883779164008226689413101)
                  ·
                    refine ⟨2581417186503085008529913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6883779164008226689413101 2581417186503085008529913)
                    ·
                      refine ⟨1936062889877313756397435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2581417186503085008529913 1936062889877313756397435)
                      ·
                        rfl

theorem cell23_3770469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_3770469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770469 prefixEnd_3770469 := by exact prefixLift 3770469
  have htrace : WordTrace (prefixWord ++ tailWord_3770469) baseStart_3770469 baseEnd_3770469 := by
    simpa [prefixWord, tailWord_3770469, baseEnd_3770469] using wordTrace_append hprefix tailTrace_3770469
  have hstable : (prefixWord ++ tailWord_3770469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770469).length < 2 ^ (prefixWord ++ tailWord_3770469).sum := by decide
  have hdescent : baseEnd_3770469 < baseStart_3770469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770555 : List Nat := [1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 4]
def baseStart_3770555 : Nat := 118140960795 + 3770555 * 2 ^ 59
def prefixEnd_3770555 : Nat := 4983230072969 + 3 ^ 40 * 3770555 * 2
def baseEnd_3770555 : Nat := 1936107049213600419922039

theorem tailTrace_3770555 : CollatzResearch.WordTrace tailWord_3770555 prefixEnd_3770555 1936107049213600419922039 := by
  unfold tailWord_3770555
  simp only [CollatzResearch.WordTrace]
  refine ⟨137523438854930669370873119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91682292569953779580582079 137523438854930669370873119)
  ·
    refine ⟨206285158282396004056309679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137523438854930669370873119 206285158282396004056309679)
    ·
      refine ⟨309427737423594006084464519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206285158282396004056309679 309427737423594006084464519)
      ·
        refine ⟨464141606135391009126696779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309427737423594006084464519 464141606135391009126696779)
        ·
          refine ⟨696212409203086513690045169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464141606135391009126696779 696212409203086513690045169)
          ·
            refine ⟨522159306902314885267533877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 696212409203086513690045169 522159306902314885267533877)
            ·
              refine ⟨48952435022092020493831301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 522159306902314885267533877 48952435022092020493831301)
              ·
                refine ⟨9178581566642253842593369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48952435022092020493831301 9178581566642253842593369)
                ·
                  refine ⟨6883936174981690381945027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9178581566642253842593369 6883936174981690381945027)
                  ·
                    refine ⟨10325904262472535572917541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6883936174981690381945027 10325904262472535572917541)
                    ·
                      refine ⟨1936107049213600419922039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10325904262472535572917541 1936107049213600419922039)
                      ·
                        rfl

theorem cell23_3770555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 4].length) (baseStart_3770555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770555 prefixEnd_3770555 := by exact prefixLift 3770555
  have htrace : WordTrace (prefixWord ++ tailWord_3770555) baseStart_3770555 baseEnd_3770555 := by
    simpa [prefixWord, tailWord_3770555, baseEnd_3770555] using wordTrace_append hprefix tailTrace_3770555
  have hstable : (prefixWord ++ tailWord_3770555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770555).length < 2 ^ (prefixWord ++ tailWord_3770555).sum := by decide
  have hdescent : baseEnd_3770555 < baseStart_3770555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770556 : List Nat := [2, 2, 2, 3, 3, 2, 2, 2, 5]
def baseStart_3770556 : Nat := 118140960795 + 3770556 * 2 ^ 59
def prefixEnd_3770556 : Nat := 4983230072969 + 3 ^ 40 * 3770556 * 2
def baseEnd_3770556 : Nat := 215123062521583879556615

theorem tailTrace_3770556 : CollatzResearch.WordTrace tailWord_3770556 prefixEnd_3770556 215123062521583879556615 := by
  unfold tailWord_3770556
  simp only [CollatzResearch.WordTrace]
  refine ⟨68761737663963523270829761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91682316885284697694439681 68761737663963523270829761)
  ·
    refine ⟨51571303247972642453122321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68761737663963523270829761 51571303247972642453122321)
    ·
      refine ⟨38678477435979481839841741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51571303247972642453122321 38678477435979481839841741)
      ·
        refine ⟨14504429038492305689940653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38678477435979481839841741 14504429038492305689940653)
        ·
          refine ⟨5439160889434614633727745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14504429038492305689940653 5439160889434614633727745)
          ·
            refine ⟨4079370667075960975295809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5439160889434614633727745 4079370667075960975295809)
            ·
              refine ⟨3059528000306970731471857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4079370667075960975295809 3059528000306970731471857)
              ·
                refine ⟨2294646000230228048603893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3059528000306970731471857 2294646000230228048603893)
                ·
                  refine ⟨215123062521583879556615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2294646000230228048603893 215123062521583879556615)
                  ·
                    rfl

theorem cell23_3770556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 5].length) (baseStart_3770556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770556 prefixEnd_3770556 := by exact prefixLift 3770556
  have htrace : WordTrace (prefixWord ++ tailWord_3770556) baseStart_3770556 baseEnd_3770556 := by
    simpa [prefixWord, tailWord_3770556, baseEnd_3770556] using wordTrace_append hprefix tailTrace_3770556
  have hstable : (prefixWord ++ tailWord_3770556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770556).length < 2 ^ (prefixWord ++ tailWord_3770556).sum := by decide
  have hdescent : baseEnd_3770556 < baseStart_3770556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770575 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 3]
def baseStart_3770575 : Nat := 118140960795 + 3770575 * 2 ^ 59
def prefixEnd_3770575 : Nat := 4983230072969 + 3 ^ 40 * 3770575 * 2
def baseEnd_3770575 : Nat := 1936117318826690341671947

theorem tailTrace_3770575 : CollatzResearch.WordTrace tailWord_3770575 prefixEnd_3770575 1936117318826690341671947 := by
  unfold tailWord_3770575
  simp only [CollatzResearch.WordTrace]
  refine ⟨137524168314858212786601179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91682778876572141857734119 137524168314858212786601179)
  ·
    refine ⟨206286252472287319179901769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137524168314858212786601179 206286252472287319179901769)
    ·
      refine ⟨154714689354215489384926327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206286252472287319179901769 154714689354215489384926327)
      ·
        refine ⟨232072034031323234077389491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154714689354215489384926327 232072034031323234077389491)
        ·
          refine ⟨348108051046984851116084237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232072034031323234077389491 348108051046984851116084237)
          ·
            refine ⟨130540519142619319168531589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348108051046984851116084237 130540519142619319168531589)
            ·
              refine ⟨24476347339241122344099673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130540519142619319168531589 24476347339241122344099673)
              ·
                refine ⟨18357260504430841758074755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24476347339241122344099673 18357260504430841758074755)
                ·
                  refine ⟨27535890756646262637112133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18357260504430841758074755 27535890756646262637112133)
                  ·
                    refine ⟨5162979516871174244458525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27535890756646262637112133 5162979516871174244458525)
                    ·
                      refine ⟨1936117318826690341671947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5162979516871174244458525 1936117318826690341671947)
                      ·
                        rfl

theorem cell23_3770575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 3].length) (baseStart_3770575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770575 prefixEnd_3770575 := by exact prefixLift 3770575
  have htrace : WordTrace (prefixWord ++ tailWord_3770575) baseStart_3770575 baseEnd_3770575 := by
    simpa [prefixWord, tailWord_3770575, baseEnd_3770575] using wordTrace_append hprefix tailTrace_3770575
  have hstable : (prefixWord ++ tailWord_3770575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770575).length < 2 ^ (prefixWord ++ tailWord_3770575).sum := by decide
  have hdescent : baseEnd_3770575 < baseStart_3770575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770589 : List Nat := [1, 4, 3, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3770589 : Nat := 118140960795 + 3770589 * 2 ^ 59
def prefixEnd_3770589 : Nat := 4983230072969 + 3 ^ 40 * 3770589 * 2
def baseEnd_3770589 : Nat := 1936124507555853286896883

theorem tailTrace_3770589 : CollatzResearch.WordTrace tailWord_3770589 prefixEnd_3770589 1936124507555853286896883 := by
  unfold tailWord_3770589
  simp only [CollatzResearch.WordTrace]
  refine ⟨137524678936807493177610821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91683119291204995451740547 137524678936807493177610821)
  ·
    refine ⟨25785877300651404970802029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137524678936807493177610821 25785877300651404970802029)
    ·
      refine ⟨9669703987744276864050761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25785877300651404970802029 9669703987744276864050761)
      ·
        refine ⟨7252277990808207648038071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9669703987744276864050761 7252277990808207648038071)
        ·
          refine ⟨10878416986212311472057107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7252277990808207648038071 10878416986212311472057107)
          ·
            refine ⟨16317625479318467208085661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10878416986212311472057107 16317625479318467208085661)
            ·
              refine ⟨6119109554744425203032123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16317625479318467208085661 6119109554744425203032123)
              ·
                refine ⟨9178664332116637804548185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6119109554744425203032123 9178664332116637804548185)
                ·
                  refine ⟨6883998249087478353411139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9178664332116637804548185 6883998249087478353411139)
                  ·
                    refine ⟨10325997373631217530116709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6883998249087478353411139 10325997373631217530116709)
                    ·
                      refine ⟨1936124507555853286896883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10325997373631217530116709 1936124507555853286896883)
                      ·
                        rfl

theorem cell23_3770589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3770589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770589 prefixEnd_3770589 := by exact prefixLift 3770589
  have htrace : WordTrace (prefixWord ++ tailWord_3770589) baseStart_3770589 baseEnd_3770589 := by
    simpa [prefixWord, tailWord_3770589, baseEnd_3770589] using wordTrace_append hprefix tailTrace_3770589
  have hstable : (prefixWord ++ tailWord_3770589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770589).length < 2 ^ (prefixWord ++ tailWord_3770589).sum := by decide
  have hdescent : baseEnd_3770589 < baseStart_3770589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770673 : List Nat := [1, 2, 2, 3, 5, 1, 1, 1, 3, 1, 3]
def baseStart_3770673 : Nat := 118140960795 + 3770673 * 2 ^ 59
def prefixEnd_3770673 : Nat := 4983230072969 + 3 ^ 40 * 3770673 * 2
def baseEnd_3770673 : Nat := 1936167639930830958246497

theorem tailTrace_3770673 : CollatzResearch.WordTrace tailWord_3770673 prefixEnd_3770673 1936167639930830958246497 := by
  unfold tailWord_3770673
  simp only [CollatzResearch.WordTrace]
  refine ⟨137527742668503175523668673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91685161779002117015779115 137527742668503175523668673)
  ·
    refine ⟨103145807001377381642751505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137527742668503175523668673 103145807001377381642751505)
    ·
      refine ⟨77359355251033036232063629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103145807001377381642751505 77359355251033036232063629)
      ·
        refine ⟨29009758219137388587023861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77359355251033036232063629 29009758219137388587023861)
        ·
          refine ⟨2719664833044130180033487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29009758219137388587023861 2719664833044130180033487)
          ·
            refine ⟨4079497249566195270050231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2719664833044130180033487 4079497249566195270050231)
            ·
              refine ⟨6119245874349292905075347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4079497249566195270050231 6119245874349292905075347)
              ·
                refine ⟨9178868811523939357613021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6119245874349292905075347 9178868811523939357613021)
                ·
                  refine ⟨3442075804321477259104883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9178868811523939357613021 3442075804321477259104883)
                  ·
                    refine ⟨5163113706482215888657325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3442075804321477259104883 5163113706482215888657325)
                    ·
                      refine ⟨1936167639930830958246497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5163113706482215888657325 1936167639930830958246497)
                      ·
                        rfl

theorem cell23_3770673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_3770673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770673 prefixEnd_3770673 := by exact prefixLift 3770673
  have htrace : WordTrace (prefixWord ++ tailWord_3770673) baseStart_3770673 baseEnd_3770673 := by
    simpa [prefixWord, tailWord_3770673, baseEnd_3770673] using wordTrace_append hprefix tailTrace_3770673
  have hstable : (prefixWord ++ tailWord_3770673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770673).length < 2 ^ (prefixWord ++ tailWord_3770673).sum := by decide
  have hdescent : baseEnd_3770673 < baseStart_3770673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770675 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 6]
def baseStart_3770675 : Nat := 118140960795 + 3770675 * 2 ^ 59
def prefixEnd_3770675 : Nat := 4983230072969 + 3 ^ 40 * 3770675 * 2
def baseEnd_3770675 : Nat := 1936168666892139950421487

theorem tailTrace_3770675 : CollatzResearch.WordTrace tailWord_3770675 prefixEnd_3770675 1936168666892139950421487 := by
  unfold tailWord_3770675
  simp only [CollatzResearch.WordTrace]
  refine ⟨137527815614495929865241479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91685210409663953243494319 137527815614495929865241479)
  ·
    refine ⟨206291723421743894797862219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137527815614495929865241479 206291723421743894797862219)
    ·
      refine ⟨309437585132615842196793329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206291723421743894797862219 309437585132615842196793329)
      ·
        refine ⟨232078188849461881647594997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309437585132615842196793329 232078188849461881647594997)
        ·
          refine ⟨21757330204637051404462031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232078188849461881647594997 21757330204637051404462031)
          ·
            refine ⟨32635995306955577106693047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21757330204637051404462031 32635995306955577106693047)
            ·
              refine ⟨48953992960433365660039571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32635995306955577106693047 48953992960433365660039571)
              ·
                refine ⟨73430989440650048490059357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48953992960433365660039571 73430989440650048490059357)
                ·
                  refine ⟨27536621040243768183772259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73430989440650048490059357 27536621040243768183772259)
                  ·
                    refine ⟨41304931560365652275658389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27536621040243768183772259 41304931560365652275658389)
                    ·
                      refine ⟨1936168666892139950421487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41304931560365652275658389 1936168666892139950421487)
                      ·
                        rfl

theorem cell23_3770675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_3770675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770675 prefixEnd_3770675 := by exact prefixLift 3770675
  have htrace : WordTrace (prefixWord ++ tailWord_3770675) baseStart_3770675 baseEnd_3770675 := by
    simpa [prefixWord, tailWord_3770675, baseEnd_3770675] using wordTrace_append hprefix tailTrace_3770675
  have hstable : (prefixWord ++ tailWord_3770675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770675).length < 2 ^ (prefixWord ++ tailWord_3770675).sum := by decide
  have hdescent : baseEnd_3770675 < baseStart_3770675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770682 : List Nat := [3, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5]
def baseStart_3770682 : Nat := 118140960795 + 3770682 * 2 ^ 59
def prefixEnd_3770682 : Nat := 4983230072969 + 3 ^ 40 * 3770682 * 2
def baseEnd_3770682 : Nat := 1936172261256721423033955

theorem tailTrace_3770682 : CollatzResearch.WordTrace tailWord_3770682 prefixEnd_3770682 1936172261256721423033955 := by
  unfold tailWord_3770682
  simp only [CollatzResearch.WordTrace]
  refine ⟨34382017731367642515186575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91685380616980380040497533 34382017731367642515186575)
  ·
    refine ⟨51573026597051463772779863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34382017731367642515186575 51573026597051463772779863)
    ·
      refine ⟨77359539895577195659169795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51573026597051463772779863 77359539895577195659169795)
      ·
        refine ⟨116039309843365793488754693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77359539895577195659169795 116039309843365793488754693)
        ·
          refine ⟨21757370595631086279141505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116039309843365793488754693 21757370595631086279141505)
          ·
            refine ⟨16318027946723314709356129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21757370595631086279141505 16318027946723314709356129)
            ·
              refine ⟨12238520960042486032017097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16318027946723314709356129 12238520960042486032017097)
              ·
                refine ⟨9178890720031864524012823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12238520960042486032017097 9178890720031864524012823)
                ·
                  refine ⟨13768336080047796786019235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9178890720031864524012823 13768336080047796786019235)
                  ·
                    refine ⟨20652504120071695179028853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13768336080047796786019235 20652504120071695179028853)
                    ·
                      refine ⟨1936172261256721423033955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20652504120071695179028853 1936172261256721423033955)
                      ·
                        rfl

theorem cell23_3770682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_3770682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770682 prefixEnd_3770682 := by exact prefixLift 3770682
  have htrace : WordTrace (prefixWord ++ tailWord_3770682) baseStart_3770682 baseEnd_3770682 := by
    simpa [prefixWord, tailWord_3770682, baseEnd_3770682] using wordTrace_append hprefix tailTrace_3770682
  have hstable : (prefixWord ++ tailWord_3770682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770682).length < 2 ^ (prefixWord ++ tailWord_3770682).sum := by decide
  have hdescent : baseEnd_3770682 < baseStart_3770682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770709 : List Nat := [1, 3, 2, 2, 4, 1, 1, 2, 1, 2, 4]
def baseStart_3770709 : Nat := 118140960795 + 3770709 * 2 ^ 59
def prefixEnd_3770709 : Nat := 4983230072969 + 3 ^ 40 * 3770709 * 2
def baseEnd_3770709 : Nat := 1936186125234392817396331

theorem tailTrace_3770709 : CollatzResearch.WordTrace tailWord_3770709 prefixEnd_3770709 1936186125234392817396331 := by
  unfold tailWord_3770709
  simp only [CollatzResearch.WordTrace]
  refine ⟨137529055696372753671979181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91686037130915169114652787 137529055696372753671979181)
  ·
    refine ⟨51573395886139782626992193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137529055696372753671979181 51573395886139782626992193)
    ·
      refine ⟨38680046914604836970244145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51573395886139782626992193 38680046914604836970244145)
      ·
        refine ⟨29010035185953627727683109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38680046914604836970244145 29010035185953627727683109)
        ·
          refine ⟨5439381597366305198940583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29010035185953627727683109 5439381597366305198940583)
          ·
            refine ⟨8159072396049457798410875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5439381597366305198940583 8159072396049457798410875)
            ·
              refine ⟨12238608594074186697616313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8159072396049457798410875 12238608594074186697616313)
              ·
                refine ⟨9178956445555640023212235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12238608594074186697616313 9178956445555640023212235)
                ·
                  refine ⟨13768434668333460034818353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9178956445555640023212235 13768434668333460034818353)
                  ·
                    refine ⟨10326326001250095026113765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13768434668333460034818353 10326326001250095026113765)
                    ·
                      refine ⟨1936186125234392817396331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10326326001250095026113765 1936186125234392817396331)
                      ·
                        rfl

theorem cell23_3770709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_3770709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770709 prefixEnd_3770709 := by exact prefixLift 3770709
  have htrace : WordTrace (prefixWord ++ tailWord_3770709) baseStart_3770709 baseEnd_3770709 := by
    simpa [prefixWord, tailWord_3770709, baseEnd_3770709] using wordTrace_append hprefix tailTrace_3770709
  have hstable : (prefixWord ++ tailWord_3770709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770709).length < 2 ^ (prefixWord ++ tailWord_3770709).sum := by decide
  have hdescent : baseEnd_3770709 < baseStart_3770709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770730 : List Nat := [3, 1, 3, 3, 1, 2, 1, 4, 1, 2, 2]
def baseStart_3770730 : Nat := 118140960795 + 3770730 * 2 ^ 59
def prefixEnd_3770730 : Nat := 4983230072969 + 3 ^ 40 * 3770730 * 2
def baseEnd_3770730 : Nat := 1936196908328137235233735

theorem tailTrace_3770730 : CollatzResearch.WordTrace tailWord_3770730 prefixEnd_3770730 1936196908328137235233735 := by
  unfold tailWord_3770730
  simp only [CollatzResearch.WordTrace]
  refine ⟨34382455407324168564623411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91686547752864449505662429 34382455407324168564623411)
  ·
    refine ⟨51573683110986252846935117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34382455407324168564623411 51573683110986252846935117)
    ·
      refine ⟨19340131166619844817600669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51573683110986252846935117 19340131166619844817600669)
      ·
        refine ⟨7252549187482441806600251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19340131166619844817600669 7252549187482441806600251)
        ·
          refine ⟨10878823781223662709900377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7252549187482441806600251 10878823781223662709900377)
          ·
            refine ⟨8159117835917747032425283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10878823781223662709900377 8159117835917747032425283)
            ·
              refine ⟨12238676753876620548637925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8159117835917747032425283 12238676753876620548637925)
              ·
                refine ⟨2294751891351866352869611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12238676753876620548637925 2294751891351866352869611)
                ·
                  refine ⟨3442127837027799529304417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2294751891351866352869611 3442127837027799529304417)
                  ·
                    refine ⟨2581595877770849646978313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3442127837027799529304417 2581595877770849646978313)
                    ·
                      refine ⟨1936196908328137235233735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2581595877770849646978313 1936196908328137235233735)
                      ·
                        rfl

theorem cell23_3770730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_3770730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770730 prefixEnd_3770730 := by exact prefixLift 3770730
  have htrace : WordTrace (prefixWord ++ tailWord_3770730) baseStart_3770730 baseEnd_3770730 := by
    simpa [prefixWord, tailWord_3770730, baseEnd_3770730] using wordTrace_append hprefix tailTrace_3770730
  have hstable : (prefixWord ++ tailWord_3770730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770730).length < 2 ^ (prefixWord ++ tailWord_3770730).sum := by decide
  have hdescent : baseEnd_3770730 < baseStart_3770730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770756 : List Nat := [2, 3, 2, 1, 1, 2, 2, 4, 1, 3, 2]
def baseStart_3770756 : Nat := 118140960795 + 3770756 * 2 ^ 59
def prefixEnd_3770756 : Nat := 4983230072969 + 3 ^ 40 * 3770756 * 2
def baseEnd_3770756 : Nat := 1936210258825154133508615

theorem tailTrace_3770756 : CollatzResearch.WordTrace tailWord_3770756 prefixEnd_3770756 1936210258825154133508615 := by
  unfold tailWord_3770756
  simp only [CollatzResearch.WordTrace]
  refine ⟨68765384963601240349470061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91687179951468320465960081 68765384963601240349470061)
  ·
    refine ⟨25787019361350465131051273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68765384963601240349470061 25787019361350465131051273)
    ·
      refine ⟨19340264521012848848288455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25787019361350465131051273 19340264521012848848288455)
      ·
        refine ⟨29010396781519273272432683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19340264521012848848288455 29010396781519273272432683)
        ·
          refine ⟨43515595172278909908649025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29010396781519273272432683 43515595172278909908649025)
          ·
            refine ⟨32636696379209182431486769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43515595172278909908649025 32636696379209182431486769)
            ·
              refine ⟨24477522284406886823615077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32636696379209182431486769 24477522284406886823615077)
              ·
                refine ⟨4589535428326291279427827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24477522284406886823615077 4589535428326291279427827)
                ·
                  refine ⟨6884303142489436919141741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4589535428326291279427827 6884303142489436919141741)
                  ·
                    refine ⟨2581613678433538844678153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6884303142489436919141741 2581613678433538844678153)
                    ·
                      refine ⟨1936210258825154133508615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2581613678433538844678153 1936210258825154133508615)
                      ·
                        rfl

theorem cell23_3770756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_3770756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770756 prefixEnd_3770756 := by exact prefixLift 3770756
  have htrace : WordTrace (prefixWord ++ tailWord_3770756) baseStart_3770756 baseEnd_3770756 := by
    simpa [prefixWord, tailWord_3770756, baseEnd_3770756] using wordTrace_append hprefix tailTrace_3770756
  have hstable : (prefixWord ++ tailWord_3770756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770756).length < 2 ^ (prefixWord ++ tailWord_3770756).sum := by decide
  have hdescent : baseEnd_3770756 < baseStart_3770756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770774 : List Nat := [5, 3, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3770774 : Nat := 118140960795 + 3770774 * 2 ^ 59
def prefixEnd_3770774 : Nat := 4983230072969 + 3 ^ 40 * 3770774 * 2
def baseEnd_3770774 : Nat := 645406500492311687694511

theorem tailTrace_3770774 : CollatzResearch.WordTrace tailWord_3770774 prefixEnd_3770774 645406500492311687694511 := by
  unfold tailWord_3770774
  simp only [CollatzResearch.WordTrace]
  refine ⟨8595714152571079360818461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91687617627424846515396917 8595714152571079360818461)
  ·
    refine ⟨3223392807214154760306923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8595714152571079360818461 3223392807214154760306923)
    ·
      refine ⟨4835089210821232140460385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3223392807214154760306923 4835089210821232140460385)
      ·
        refine ⟨3626316908115924105345289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4835089210821232140460385 3626316908115924105345289)
        ·
          refine ⟨2719737681086943079008967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3626316908115924105345289 2719737681086943079008967)
          ·
            refine ⟨4079606521630414618513451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2719737681086943079008967 4079606521630414618513451)
            ·
              refine ⟨6119409782445621927770177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4079606521630414618513451 6119409782445621927770177)
              ·
                refine ⟨4589557336834216445827633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6119409782445621927770177 4589557336834216445827633)
                ·
                  refine ⟨3442168002625662334370725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4589557336834216445827633 3442168002625662334370725)
                  ·
                    refine ⟨645406500492311687694511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3442168002625662334370725 645406500492311687694511)
                    ·
                      rfl

theorem cell23_3770774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3770774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770774 prefixEnd_3770774 := by exact prefixLift 3770774
  have htrace : WordTrace (prefixWord ++ tailWord_3770774) baseStart_3770774 baseEnd_3770774 := by
    simpa [prefixWord, tailWord_3770774, baseEnd_3770774] using wordTrace_append hprefix tailTrace_3770774
  have hstable : (prefixWord ++ tailWord_3770774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770774).length < 2 ^ (prefixWord ++ tailWord_3770774).sum := by decide
  have hdescent : baseEnd_3770774 < baseStart_3770774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770859 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 1, 6, 2]
def baseStart_3770859 : Nat := 118140960795 + 3770859 * 2 ^ 59
def prefixEnd_3770859 : Nat := 4983230072969 + 3 ^ 40 * 3770859 * 2
def baseEnd_3770859 : Nat := 1936263147332567230520641

theorem tailTrace_3770859 : CollatzResearch.WordTrace tailWord_3770859 prefixEnd_3770859 1936263147332567230520641 := by
  unfold tailWord_3770859
  simp only [CollatzResearch.WordTrace]
  refine ⟨137534526645829329289939631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91689684430552886193293087 137534526645829329289939631)
  ·
    refine ⟨206301789968743993934909447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137534526645829329289939631 206301789968743993934909447)
    ·
      refine ⟨309452684953115990902364171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206301789968743993934909447 309452684953115990902364171)
      ·
        refine ⟨464179027429673986353546257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309452684953115990902364171 464179027429673986353546257)
        ·
          refine ⟨348134270572255489765159693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464179027429673986353546257 348134270572255489765159693)
          ·
            refine ⟨130550351464595808661934885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348134270572255489765159693 130550351464595808661934885)
            ·
              refine ⟨24478190899611714124112791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130550351464595808661934885 24478190899611714124112791)
              ·
                refine ⟨36717286349417571186169187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24478190899611714124112791 36717286349417571186169187)
                ·
                  refine ⟨55075929524126356779253781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36717286349417571186169187 55075929524126356779253781)
                  ·
                    refine ⟨2581684196443422974027521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55075929524126356779253781 2581684196443422974027521)
                    ·
                      refine ⟨1936263147332567230520641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2581684196443422974027521 1936263147332567230520641)
                      ·
                        rfl

theorem cell23_3770859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 6, 2].length) (baseStart_3770859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770859 prefixEnd_3770859 := by exact prefixLift 3770859
  have htrace : WordTrace (prefixWord ++ tailWord_3770859) baseStart_3770859 baseEnd_3770859 := by
    simpa [prefixWord, tailWord_3770859, baseEnd_3770859] using wordTrace_append hprefix tailTrace_3770859
  have hstable : (prefixWord ++ tailWord_3770859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770859).length < 2 ^ (prefixWord ++ tailWord_3770859).sum := by decide
  have hdescent : baseEnd_3770859 < baseStart_3770859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770899 : List Nat := [1, 1, 1, 2, 1, 5, 4, 2, 6]
def baseStart_3770899 : Nat := 118140960795 + 3770899 * 2 ^ 59
def prefixEnd_3770899 : Nat := 4983230072969 + 3 ^ 40 * 3770899 * 2
def baseEnd_3770899 : Nat := 215142631839860786002273

theorem tailTrace_3770899 : CollatzResearch.WordTrace tailWord_3770899 prefixEnd_3770899 215142631839860786002273 := by
  unfold tailWord_3770899
  simp only [CollatzResearch.WordTrace]
  refine ⟨137535985565684416121395751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91690657043789610747597167 137535985565684416121395751)
  ·
    refine ⟨206303978348526624182093627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137535985565684416121395751 206303978348526624182093627)
    ·
      refine ⟨309455967522789936273140441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206303978348526624182093627 309455967522789936273140441)
      ·
        refine ⟨232091975642092452204855331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309455967522789936273140441 232091975642092452204855331)
        ·
          refine ⟨348137963463138678307282997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232091975642092452204855331 348137963463138678307282997)
          ·
            refine ⟨32637934074669251091307781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 348137963463138678307282997 32637934074669251091307781)
            ·
              refine ⟨6119612639000484579620209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32637934074669251091307781 6119612639000484579620209)
              ·
                refine ⟨4589709479250363434715157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6119612639000484579620209 4589709479250363434715157)
                ·
                  refine ⟨215142631839860786002273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4589709479250363434715157 215142631839860786002273)
                  ·
                    rfl

theorem cell23_3770899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 6].length) (baseStart_3770899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770899 prefixEnd_3770899 := by exact prefixLift 3770899
  have htrace : WordTrace (prefixWord ++ tailWord_3770899) baseStart_3770899 baseEnd_3770899 := by
    simpa [prefixWord, tailWord_3770899, baseEnd_3770899] using wordTrace_append hprefix tailTrace_3770899
  have hstable : (prefixWord ++ tailWord_3770899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770899).length < 2 ^ (prefixWord ++ tailWord_3770899).sum := by decide
  have hdescent : baseEnd_3770899 < baseStart_3770899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770929 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 3, 5]
def baseStart_3770929 : Nat := 118140960795 + 3770929 * 2 ^ 59
def prefixEnd_3770929 : Nat := 4983230072969 + 3 ^ 40 * 3770929 * 2
def baseEnd_3770929 : Nat := 645433030326127318881773

theorem tailTrace_3770929 : CollatzResearch.WordTrace tailWord_3770929 prefixEnd_3770929 645433030326127318881773 := by
  unfold tailWord_3770929
  simp only [CollatzResearch.WordTrace]
  refine ⟨137537079755575731244987841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91691386503717154163325227 137537079755575731244987841)
  ·
    refine ⟨103152809816681798433740881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137537079755575731244987841 103152809816681798433740881)
    ·
      refine ⟨77364607362511348825305661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103152809816681798433740881 77364607362511348825305661)
      ·
        refine ⟨29011727760941755809489623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77364607362511348825305661 29011727760941755809489623)
        ·
          refine ⟨43517591641412633714234435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29011727760941755809489623 43517591641412633714234435)
          ·
            refine ⟨65276387462118950571351653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43517591641412633714234435 65276387462118950571351653)
            ·
              refine ⟨12239322649147303232128435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65276387462118950571351653 12239322649147303232128435)
              ·
                refine ⟨18358983973720954848192653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12239322649147303232128435 18358983973720954848192653)
                ·
                  refine ⟨6884618990145358068072245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18358983973720954848192653 6884618990145358068072245)
                  ·
                    refine ⟨645433030326127318881773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6884618990145358068072245 645433030326127318881773)
                    ·
                      rfl

theorem cell23_3770929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_3770929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770929 prefixEnd_3770929 := by exact prefixLift 3770929
  have htrace : WordTrace (prefixWord ++ tailWord_3770929) baseStart_3770929 baseEnd_3770929 := by
    simpa [prefixWord, tailWord_3770929, baseEnd_3770929] using wordTrace_append hprefix tailTrace_3770929
  have hstable : (prefixWord ++ tailWord_3770929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770929).length < 2 ^ (prefixWord ++ tailWord_3770929).sum := by decide
  have hdescent : baseEnd_3770929 < baseStart_3770929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770936 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 1, 5, 2]
def baseStart_3770936 : Nat := 118140960795 + 3770936 * 2 ^ 59
def prefixEnd_3770936 : Nat := 4983230072969 + 3 ^ 40 * 3770936 * 2
def baseEnd_3770936 : Nat := 1936302685342963429257787

theorem tailTrace_3770936 : CollatzResearch.WordTrace tailWord_3770936 prefixEnd_3770936 1936302685342963429257787 := by
  unfold tailWord_3770936
  simp only [CollatzResearch.WordTrace]
  refine ⟨68768667533275185720246331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91691556711033580960328441 68768667533275185720246331)
  ·
    refine ⟨103153001299912778580369497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68768667533275185720246331 103153001299912778580369497)
    ·
      refine ⟨77364750974934583935277123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103153001299912778580369497 77364750974934583935277123)
      ·
        refine ⟨116047126462401875902915685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77364750974934583935277123 116047126462401875902915685)
        ·
          refine ⟨21758836211700351731796691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116047126462401875902915685 21758836211700351731796691)
          ·
            refine ⟨32638254317550527597695037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21758836211700351731796691 32638254317550527597695037)
            ·
              refine ⟨12239345369081447849135639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32638254317550527597695037 12239345369081447849135639)
              ·
                refine ⟨18359018053622171773703459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12239345369081447849135639 18359018053622171773703459)
                ·
                  refine ⟨27538527080433257660555189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18359018053622171773703459 27538527080433257660555189)
                  ·
                    refine ⟨2581736913790617905677049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27538527080433257660555189 2581736913790617905677049)
                    ·
                      refine ⟨1936302685342963429257787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2581736913790617905677049 1936302685342963429257787)
                      ·
                        rfl

theorem cell23_3770936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 1, 5, 2].length) (baseStart_3770936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770936 prefixEnd_3770936 := by exact prefixLift 3770936
  have htrace : WordTrace (prefixWord ++ tailWord_3770936) baseStart_3770936 baseEnd_3770936 := by
    simpa [prefixWord, tailWord_3770936, baseEnd_3770936] using wordTrace_append hprefix tailTrace_3770936
  have hstable : (prefixWord ++ tailWord_3770936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770936).length < 2 ^ (prefixWord ++ tailWord_3770936).sum := by decide
  have hdescent : baseEnd_3770936 < baseStart_3770936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770950 : List Nat := [6, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_3770950 : Nat := 118140960795 + 3770950 * 2 ^ 59
def prefixEnd_3770950 : Nat := 4983230072969 + 3 ^ 40 * 3770950 * 2
def baseEnd_3770950 : Nat := 215145541563569597164747

theorem tailTrace_3770950 : CollatzResearch.WordTrace tailWord_3770950 prefixEnd_3770950 215145541563569597164747 := by
  unfold tailWord_3770950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4298057677765614119734447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91691897125666434554334869 4298057677765614119734447)
  ·
    refine ⟨6447086516648421179601671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4298057677765614119734447 6447086516648421179601671)
    ·
      refine ⟨9670629774972631769402507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6447086516648421179601671 9670629774972631769402507)
      ·
        refine ⟨14505944662458947654103761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9670629774972631769402507 14505944662458947654103761)
        ·
          refine ⟨10879458496844210740577821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14505944662458947654103761 10879458496844210740577821)
          ·
            refine ⟨4079796936316579027716683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10879458496844210740577821 4079796936316579027716683)
            ·
              refine ⟨6119695404474868541575025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4079796936316579027716683 6119695404474868541575025)
              ·
                refine ⟨4589771553356151406181269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6119695404474868541575025 4589771553356151406181269)
                ·
                  refine ⟨215145541563569597164747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4589771553356151406181269 215145541563569597164747)
                  ·
                    rfl

theorem cell23_3770950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_3770950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770950 prefixEnd_3770950 := by exact prefixLift 3770950
  have htrace : WordTrace (prefixWord ++ tailWord_3770950) baseStart_3770950 baseEnd_3770950 := by
    simpa [prefixWord, tailWord_3770950, baseEnd_3770950] using wordTrace_append hprefix tailTrace_3770950
  have hstable : (prefixWord ++ tailWord_3770950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770950).length < 2 ^ (prefixWord ++ tailWord_3770950).sum := by decide
  have hdescent : baseEnd_3770950 < baseStart_3770950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770976 : List Nat := [2, 1, 1, 3, 2, 1, 2, 5, 2, 4]
def baseStart_3770976 : Nat := 118140960795 + 3770976 * 2 ^ 59
def prefixEnd_3770976 : Nat := 4983230072969 + 3 ^ 40 * 3770976 * 2
def baseEnd_3770976 : Nat := 645441074856381090919201

theorem tailTrace_3770976 : CollatzResearch.WordTrace tailWord_3770976 prefixEnd_3770976 645441074856381090919201 := by
  unfold tailWord_3770976
  simp only [CollatzResearch.WordTrace]
  refine ⟨68769396993202729135974391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91692529324270305514632521 68769396993202729135974391)
  ·
    refine ⟨103154095489804093703961587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68769396993202729135974391 103154095489804093703961587)
    ·
      refine ⟨154731143234706140555942381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103154095489804093703961587 154731143234706140555942381)
      ·
        refine ⟨58024178713014802708478393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154731143234706140555942381 58024178713014802708478393)
        ·
          refine ⟨43518134034761102031358795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58024178713014802708478393 43518134034761102031358795)
          ·
            refine ⟨65277201052141653047038193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43518134034761102031358795 65277201052141653047038193)
            ·
              refine ⟨48957900789106239785278645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65277201052141653047038193 48957900789106239785278645)
              ·
                refine ⟨4589803198978709979869873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48957900789106239785278645 4589803198978709979869873)
                ·
                  refine ⟨3442352399234032484902405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4589803198978709979869873 3442352399234032484902405)
                  ·
                    refine ⟨645441074856381090919201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3442352399234032484902405 645441074856381090919201)
                    ·
                      rfl

theorem cell23_3770976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 2, 4].length) (baseStart_3770976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770976 prefixEnd_3770976 := by exact prefixLift 3770976
  have htrace : WordTrace (prefixWord ++ tailWord_3770976) baseStart_3770976 baseEnd_3770976 := by
    simpa [prefixWord, tailWord_3770976, baseEnd_3770976] using wordTrace_append hprefix tailTrace_3770976
  have hstable : (prefixWord ++ tailWord_3770976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770976).length < 2 ^ (prefixWord ++ tailWord_3770976).sum := by decide
  have hdescent : baseEnd_3770976 < baseStart_3770976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770979 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 6]
def baseStart_3770979 : Nat := 118140960795 + 3770979 * 2 ^ 59
def prefixEnd_3770979 : Nat := 4983230072969 + 3 ^ 40 * 3770979 * 2
def baseEnd_3770979 : Nat := 1936324765011106761020089

theorem tailTrace_3770979 : CollatzResearch.WordTrace tailWord_3770979 prefixEnd_3770979 1936324765011106761020089 := by
  unfold tailWord_3770979
  simp only [CollatzResearch.WordTrace]
  refine ⟨137538903405394589784307991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91692602270263059856205327 137538903405394589784307991)
  ·
    refine ⟨206308355108091884676461987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137538903405394589784307991 206308355108091884676461987)
    ·
      refine ⟨309462532662137827014692981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206308355108091884676461987 309462532662137827014692981)
      ·
        refine ⟨29012112437075421282627467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 309462532662137827014692981 29012112437075421282627467)
        ·
          refine ⟨43518168655613131923941201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29012112437075421282627467 43518168655613131923941201)
          ·
            refine ⟨32638626491709848942955901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43518168655613131923941201 32638626491709848942955901)
            ·
              refine ⟨12239484934391193353608463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32638626491709848942955901 12239484934391193353608463)
              ·
                refine ⟨18359227401586790030412695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12239484934391193353608463 18359227401586790030412695)
                ·
                  refine ⟨27538841102380185045619043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18359227401586790030412695 27538841102380185045619043)
                  ·
                    refine ⟨41308261653570277568428565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27538841102380185045619043 41308261653570277568428565)
                    ·
                      refine ⟨1936324765011106761020089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41308261653570277568428565 1936324765011106761020089)
                      ·
                        rfl

theorem cell23_3770979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_3770979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770979 prefixEnd_3770979 := by exact prefixLift 3770979
  have htrace : WordTrace (prefixWord ++ tailWord_3770979) baseStart_3770979 baseEnd_3770979 := by
    simpa [prefixWord, tailWord_3770979, baseEnd_3770979] using wordTrace_append hprefix tailTrace_3770979
  have hstable : (prefixWord ++ tailWord_3770979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770979).length < 2 ^ (prefixWord ++ tailWord_3770979).sum := by decide
  have hdescent : baseEnd_3770979 < baseStart_3770979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770994 : List Nat := [3, 2, 1, 2, 5, 1, 1, 3, 1, 1, 3]
def baseStart_3770994 : Nat := 118140960795 + 3770994 * 2 ^ 59
def prefixEnd_3770994 : Nat := 4983230072969 + 3 ^ 40 * 3770994 * 2
def baseEnd_3770994 : Nat := 1936332467220924202332521

theorem tailTrace_3770994 : CollatzResearch.WordTrace tailWord_3770994 prefixEnd_3770994 1936332467220924202332521 := by
  unfold tailWord_3770994
  simp only [CollatzResearch.WordTrace]
  refine ⟨34384862625085061836526009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91692967000226831564069357 34384862625085061836526009)
  ·
    refine ⟨25788646968813796377394507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34384862625085061836526009 25788646968813796377394507)
    ·
      refine ⟨38682970453220694566091761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25788646968813796377394507 38682970453220694566091761)
      ·
        refine ⟨29012227839915520924568821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38682970453220694566091761 29012227839915520924568821)
        ·
          refine ⟨2719896359992080086678327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29012227839915520924568821 2719896359992080086678327)
          ·
            refine ⟨4079844539988120130017491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2719896359992080086678327 4079844539988120130017491)
            ·
              refine ⟨6119766809982180195026237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4079844539988120130017491 6119766809982180195026237)
              ·
                refine ⟨2294912553743317573134839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6119766809982180195026237 2294912553743317573134839)
                ·
                  refine ⟨3442368830614976359702259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2294912553743317573134839 3442368830614976359702259)
                  ·
                    refine ⟨5163553245922464539553389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3442368830614976359702259 5163553245922464539553389)
                    ·
                      refine ⟨1936332467220924202332521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5163553245922464539553389 1936332467220924202332521)
                      ·
                        rfl

theorem cell23_3770994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_3770994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3770994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3770994 prefixEnd_3770994 := by exact prefixLift 3770994
  have htrace : WordTrace (prefixWord ++ tailWord_3770994) baseStart_3770994 baseEnd_3770994 := by
    simpa [prefixWord, tailWord_3770994, baseEnd_3770994] using wordTrace_append hprefix tailTrace_3770994
  have hstable : (prefixWord ++ tailWord_3770994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770994).length < 2 ^ (prefixWord ++ tailWord_3770994).sum := by decide
  have hdescent : baseEnd_3770994 < baseStart_3770994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771033 : List Nat := [1, 2, 1, 2, 1, 2, 5, 3, 2, 1, 3]
def baseStart_3771033 : Nat := 118140960795 + 3771033 * 2 ^ 59
def prefixEnd_3771033 : Nat := 4983230072969 + 3 ^ 40 * 3771033 * 2
def baseEnd_3771033 : Nat := 1936352492966449549744841

theorem tailTrace_3771033 : CollatzResearch.WordTrace tailWord_3771033 prefixEnd_3771033 1936352492966449549744841 := by
  unfold tailWord_3771033
  simp only [CollatzResearch.WordTrace]
  refine ⟨137540872947198957006773753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91693915298132638004515835 137540872947198957006773753)
  ·
    refine ⟨103155654710399217755080315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137540872947198957006773753 103155654710399217755080315)
    ·
      refine ⟨154733482065598826632620473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103155654710399217755080315 154733482065598826632620473)
      ·
        refine ⟨116050111549199119974465355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154733482065598826632620473 116050111549199119974465355)
        ·
          refine ⟨174075167323798679961698033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116050111549199119974465355 174075167323798679961698033)
          ·
            refine ⟨130556375492849009971273525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174075167323798679961698033 130556375492849009971273525)
            ·
              refine ⟨12239660202454594684806893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130556375492849009971273525 12239660202454594684806893)
              ·
                refine ⟨4589872575920473006802585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12239660202454594684806893 4589872575920473006802585)
                ·
                  refine ⟨3442404431940354755101939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4589872575920473006802585 3442404431940354755101939)
                  ·
                    refine ⟨5163606647910532132652909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3442404431940354755101939 5163606647910532132652909)
                    ·
                      refine ⟨1936352492966449549744841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5163606647910532132652909 1936352492966449549744841)
                      ·
                        rfl

theorem cell23_3771033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 1, 3].length) (baseStart_3771033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771033 prefixEnd_3771033 := by exact prefixLift 3771033
  have htrace : WordTrace (prefixWord ++ tailWord_3771033) baseStart_3771033 baseEnd_3771033 := by
    simpa [prefixWord, tailWord_3771033, baseEnd_3771033] using wordTrace_append hprefix tailTrace_3771033
  have hstable : (prefixWord ++ tailWord_3771033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771033).length < 2 ^ (prefixWord ++ tailWord_3771033).sum := by decide
  have hdescent : baseEnd_3771033 < baseStart_3771033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771043 : List Nat := [1, 1, 1, 4, 1, 1, 2, 6, 1, 3, 2]
def baseStart_3771043 : Nat := 118140960795 + 3771043 * 2 ^ 59
def prefixEnd_3771043 : Nat := 4983230072969 + 3 ^ 40 * 3771043 * 2
def baseEnd_3771043 : Nat := 1936357627772994510619795

theorem tailTrace_3771043 : CollatzResearch.WordTrace tailWord_3771043 prefixEnd_3771043 1936357627772994510619795 := by
  unfold tailWord_3771043
  simp only [CollatzResearch.WordTrace]
  refine ⟨137541237677162728714637783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91694158451441819143091855 137541237677162728714637783)
  ·
    refine ⟨206311856515744093071956675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137541237677162728714637783 206311856515744093071956675)
    ·
      refine ⟨309467784773616139607935013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206311856515744093071956675 309467784773616139607935013)
      ·
        refine ⟨58025209645053026176487815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309467784773616139607935013 58025209645053026176487815)
        ·
          refine ⟨87037814467579539264731723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58025209645053026176487815 87037814467579539264731723)
          ·
            refine ⟨130556721701369308897097585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87037814467579539264731723 130556721701369308897097585)
            ·
              refine ⟨97917541276026981672823189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130556721701369308897097585 97917541276026981672823189)
              ·
                refine ⟨4589884747313764765913587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97917541276026981672823189 4589884747313764765913587)
                ·
                  refine ⟨6884827120970647148870381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4589884747313764765913587 6884827120970647148870381)
                  ·
                    refine ⟨2581810170363992680826393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6884827120970647148870381 2581810170363992680826393)
                    ·
                      refine ⟨1936357627772994510619795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2581810170363992680826393 1936357627772994510619795)
                      ·
                        rfl

theorem cell23_3771043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_3771043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771043 prefixEnd_3771043 := by exact prefixLift 3771043
  have htrace : WordTrace (prefixWord ++ tailWord_3771043) baseStart_3771043 baseEnd_3771043 := by
    simpa [prefixWord, tailWord_3771043, baseEnd_3771043] using wordTrace_append hprefix tailTrace_3771043
  have hstable : (prefixWord ++ tailWord_3771043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771043).length < 2 ^ (prefixWord ++ tailWord_3771043).sum := by decide
  have hdescent : baseEnd_3771043 < baseStart_3771043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771086 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_3771086 : Nat := 118140960795 + 3771086 * 2 ^ 59
def prefixEnd_3771086 : Nat := 4983230072969 + 3 ^ 40 * 3771086 * 2
def baseEnd_3771086 : Nat := 1936379707441137842382097

theorem tailTrace_3771086 : CollatzResearch.WordTrace tailWord_3771086 prefixEnd_3771086 1936379707441137842382097 := by
  unfold tailWord_3771086
  simp only [CollatzResearch.WordTrace]
  refine ⟨17192850752000868382306639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91695204010671298038968741 17192850752000868382306639)
  ·
    refine ⟨25789276128001302573459959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17192850752000868382306639 25789276128001302573459959)
    ·
      refine ⟨38683914192001953860189939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25789276128001302573459959 38683914192001953860189939)
      ·
        refine ⟨58025871288002930790284909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38683914192001953860189939 58025871288002930790284909)
        ·
          refine ⟨21759701733001099046356841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58025871288002930790284909 21759701733001099046356841)
          ·
            refine ⟨16319776299750824284767631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21759701733001099046356841 16319776299750824284767631)
            ·
              refine ⟨24479664449626236427151447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16319776299750824284767631 24479664449626236427151447)
              ·
                refine ⟨36719496674439354640727171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24479664449626236427151447 36719496674439354640727171)
                ·
                  refine ⟨55079245011659031961090757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36719496674439354640727171 55079245011659031961090757)
                  ·
                    refine ⟨10327358439686068492704517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55079245011659031961090757 10327358439686068492704517)
                    ·
                      refine ⟨1936379707441137842382097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10327358439686068492704517 1936379707441137842382097)
                      ·
                        rfl

theorem cell23_3771086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_3771086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771086 prefixEnd_3771086 := by exact prefixLift 3771086
  have htrace : WordTrace (prefixWord ++ tailWord_3771086) baseStart_3771086 baseEnd_3771086 := by
    simpa [prefixWord, tailWord_3771086, baseEnd_3771086] using wordTrace_append hprefix tailTrace_3771086
  have hstable : (prefixWord ++ tailWord_3771086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771086).length < 2 ^ (prefixWord ++ tailWord_3771086).sum := by decide
  have hdescent : baseEnd_3771086 < baseStart_3771086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771096 : List Nat := [2, 1, 2, 2, 3, 3, 1, 2, 7]
def baseStart_3771096 : Nat := 118140960795 + 3771096 * 2 ^ 59
def prefixEnd_3771096 : Nat := 4983230072969 + 3 ^ 40 * 3771096 * 2
def baseEnd_3771096 : Nat := 215153871360853644806339

theorem tailTrace_3771096 : CollatzResearch.WordTrace tailWord_3771096 prefixEnd_3771096 215153871360853644806339 := by
  unfold tailWord_3771096
  simp only [CollatzResearch.WordTrace]
  refine ⟨68771585372985359383158571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91695447163980479177544761 68771585372985359383158571)
  ·
    refine ⟨103157378059478039074737857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68771585372985359383158571 103157378059478039074737857)
    ·
      refine ⟨77368033544608529306053393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103157378059478039074737857 77368033544608529306053393)
      ·
        refine ⟨58026025158456396979540045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77368033544608529306053393 58026025158456396979540045)
        ·
          refine ⟨21759759434421148867327517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58026025158456396979540045 21759759434421148867327517)
          ·
            refine ⟨8159909787907930825247819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21759759434421148867327517 8159909787907930825247819)
            ·
              refine ⟨12239864681861896237871729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8159909787907930825247819 12239864681861896237871729)
              ·
                refine ⟨9179898511396422178403797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12239864681861896237871729 9179898511396422178403797)
                ·
                  refine ⟨215153871360853644806339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9179898511396422178403797 215153871360853644806339)
                  ·
                    rfl

theorem cell23_3771096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 7].length) (baseStart_3771096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771096 prefixEnd_3771096 := by exact prefixLift 3771096
  have htrace : WordTrace (prefixWord ++ tailWord_3771096) baseStart_3771096 baseEnd_3771096 := by
    simpa [prefixWord, tailWord_3771096, baseEnd_3771096] using wordTrace_append hprefix tailTrace_3771096
  have hstable : (prefixWord ++ tailWord_3771096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771096).length < 2 ^ (prefixWord ++ tailWord_3771096).sum := by decide
  have hdescent : baseEnd_3771096 < baseStart_3771096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771146 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_3771146 : Nat := 118140960795 + 3771146 * 2 ^ 59
def prefixEnd_3771146 : Nat := 4983230072969 + 3 ^ 40 * 3771146 * 2
def baseEnd_3771146 : Nat := 1936410516280407607631821

theorem tailTrace_3771146 : CollatzResearch.WordTrace tailWord_3771146 prefixEnd_3771146 1936410516280407607631821 := by
  unfold tailWord_3771146
  simp only [CollatzResearch.WordTrace]
  refine ⟨34386248598947394326409323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91696662930526384870424861 34386248598947394326409323)
  ·
    refine ⟨51579372898421091489613985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34386248598947394326409323 51579372898421091489613985)
    ·
      refine ⟨38684529673815818617210489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51579372898421091489613985 38684529673815818617210489)
      ·
        refine ⟨29013397255361863962907867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38684529673815818617210489 29013397255361863962907867)
        ·
          refine ⟨43520095883042795944361801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29013397255361863962907867 43520095883042795944361801)
          ·
            refine ⟨32640071912282096958271351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43520095883042795944361801 32640071912282096958271351)
            ·
              refine ⟨48960107868423145437407027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32640071912282096958271351 48960107868423145437407027)
              ·
                refine ⟨73440161802634718156110541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48960107868423145437407027 73440161802634718156110541)
                ·
                  refine ⟨27540060675988019308541453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73440161802634718156110541 27540060675988019308541453)
                  ·
                    refine ⟨10327522753495507240703045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27540060675988019308541453 10327522753495507240703045)
                    ·
                      refine ⟨1936410516280407607631821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10327522753495507240703045 1936410516280407607631821)
                      ·
                        rfl

theorem cell23_3771146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_3771146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771146 prefixEnd_3771146 := by exact prefixLift 3771146
  have htrace : WordTrace (prefixWord ++ tailWord_3771146) baseStart_3771146 baseEnd_3771146 := by
    simpa [prefixWord, tailWord_3771146, baseEnd_3771146] using wordTrace_append hprefix tailTrace_3771146
  have hstable : (prefixWord ++ tailWord_3771146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771146).length < 2 ^ (prefixWord ++ tailWord_3771146).sum := by decide
  have hdescent : baseEnd_3771146 < baseStart_3771146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771186 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 8]
def baseStart_3771186 : Nat := 118140960795 + 3771186 * 2 ^ 59
def prefixEnd_3771186 : Nat := 4983230072969 + 3 ^ 40 * 3771186 * 2
def baseEnd_3771186 : Nat := 215159006167398605681293

theorem tailTrace_3771186 : CollatzResearch.WordTrace tailWord_3771186 prefixEnd_3771186 215159006167398605681293 := by
  unfold tailWord_3771186
  simp only [CollatzResearch.WordTrace]
  refine ⟨34386613328911166034273353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91697635543763109424728941 34386613328911166034273353)
  ·
    refine ⟨25789959996683374525705015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34386613328911166034273353 25789959996683374525705015)
    ·
      refine ⟨38684939995025061788557523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25789959996683374525705015 38684939995025061788557523)
      ·
        refine ⟨58027409992537592682836285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38684939995025061788557523 58027409992537592682836285)
        ·
          refine ⟨21760278747201597256063607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58027409992537592682836285 21760278747201597256063607)
          ·
            refine ⟨32640418120802395884095411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21760278747201597256063607 32640418120802395884095411)
            ·
              refine ⟨48960627181203593826143117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32640418120802395884095411 48960627181203593826143117)
              ·
                refine ⟨18360235192951347684803669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48960627181203593826143117 18360235192951347684803669)
                ·
                  refine ⟨215159006167398605681293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18360235192951347684803669 215159006167398605681293)
                  ·
                    rfl

theorem cell23_3771186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_3771186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771186 prefixEnd_3771186 := by exact prefixLift 3771186
  have htrace : WordTrace (prefixWord ++ tailWord_3771186) baseStart_3771186 baseEnd_3771186 := by
    simpa [prefixWord, tailWord_3771186, baseEnd_3771186] using wordTrace_append hprefix tailTrace_3771186
  have hstable : (prefixWord ++ tailWord_3771186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771186).length < 2 ^ (prefixWord ++ tailWord_3771186).sum := by decide
  have hdescent : baseEnd_3771186 < baseStart_3771186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771274 : List Nat := [3, 1, 2, 4, 1, 3, 1, 1, 2, 3, 2]
def baseStart_3771274 : Nat := 118140960795 + 3771274 * 2 ^ 59
def prefixEnd_3771274 : Nat := 4983230072969 + 3 ^ 40 * 3771274 * 2
def baseEnd_3771274 : Nat := 1936476241804183106831233

theorem tailTrace_3771274 : CollatzResearch.WordTrace tailWord_3771274 prefixEnd_3771274 1936476241804183106831233 := by
  unfold tailWord_3771274
  simp only [CollatzResearch.WordTrace]
  refine ⟨34387415734831463791574219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91699775292883903444197917 34387415734831463791574219)
  ·
    refine ⟨51581123602247195687361329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34387415734831463791574219 51581123602247195687361329)
    ·
      refine ⟨38685842701685396765520997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51581123602247195687361329 38685842701685396765520997)
      ·
        refine ⟨7253595506566011893535187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38685842701685396765520997 7253595506566011893535187)
        ·
          refine ⟨10880393259849017840302781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7253595506566011893535187 10880393259849017840302781)
          ·
            refine ⟨4080147472443381690113543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10880393259849017840302781 4080147472443381690113543)
            ·
              refine ⟨6120221208665072535170315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4080147472443381690113543 6120221208665072535170315)
              ·
                refine ⟨9180331812997608802755473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6120221208665072535170315 9180331812997608802755473)
                ·
                  refine ⟨6885248859748206602066605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9180331812997608802755473 6885248859748206602066605)
                  ·
                    refine ⟨2581968322405577475774977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6885248859748206602066605 2581968322405577475774977)
                    ·
                      refine ⟨1936476241804183106831233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2581968322405577475774977 1936476241804183106831233)
                      ·
                        rfl

theorem cell23_3771274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_3771274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771274 prefixEnd_3771274 := by exact prefixLift 3771274
  have htrace : WordTrace (prefixWord ++ tailWord_3771274) baseStart_3771274 baseEnd_3771274 := by
    simpa [prefixWord, tailWord_3771274, baseEnd_3771274] using wordTrace_append hprefix tailTrace_3771274
  have hstable : (prefixWord ++ tailWord_3771274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771274).length < 2 ^ (prefixWord ++ tailWord_3771274).sum := by decide
  have hdescent : baseEnd_3771274 < baseStart_3771274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771276 : List Nat := [2, 2, 1, 2, 1, 2, 2, 11]
def baseStart_3771276 : Nat := 118140960795 + 3771276 * 2 ^ 59
def prefixEnd_3771276 : Nat := 4983230072969 + 3 ^ 40 * 3771276 * 2
def baseEnd_3771276 : Nat := 71721380324647855518749

theorem tailTrace_3771276 : CollatzResearch.WordTrace tailWord_3771276 prefixEnd_3771276 71721380324647855518749 := by
  unfold tailWord_3771276
  simp only [CollatzResearch.WordTrace]
  refine ⟨68774867942659304753934841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91699823923545739671913121 68774867942659304753934841)
  ·
    refine ⟨51581150956994478565451131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68774867942659304753934841 51581150956994478565451131)
    ·
      refine ⟨77371726435491717848176697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51581150956994478565451131 77371726435491717848176697)
      ·
        refine ⟨58028794826618788386132523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77371726435491717848176697 58028794826618788386132523)
        ·
          refine ⟨87043192239928182579198785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58028794826618788386132523 87043192239928182579198785)
          ·
            refine ⟨65282394179946136934399089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87043192239928182579198785 65282394179946136934399089)
            ·
              refine ⟨48961795634959602700799317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65282394179946136934399089 48961795634959602700799317)
              ·
                refine ⟨71721380324647855518749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 48961795634959602700799317 71721380324647855518749)
                ·
                  rfl

theorem cell23_3771276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 11].length) (baseStart_3771276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771276 prefixEnd_3771276 := by exact prefixLift 3771276
  have htrace : WordTrace (prefixWord ++ tailWord_3771276) baseStart_3771276 baseEnd_3771276 := by
    simpa [prefixWord, tailWord_3771276, baseEnd_3771276] using wordTrace_append hprefix tailTrace_3771276
  have hstable : (prefixWord ++ tailWord_3771276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771276).length < 2 ^ (prefixWord ++ tailWord_3771276).sum := by decide
  have hdescent : baseEnd_3771276 < baseStart_3771276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771297 : List Nat := [1, 2, 3, 4, 1, 1, 3, 2, 2, 4]
def baseStart_3771297 : Nat := 118140960795 + 3771297 * 2 ^ 59
def prefixEnd_3771297 : Nat := 4983230072969 + 3 ^ 40 * 3771297 * 2
def baseEnd_3771297 : Nat := 645496017286412172281209

theorem tailTrace_3771297 : CollatzResearch.WordTrace tailWord_3771297 prefixEnd_3771297 645496017286412172281209 := by
  unfold tailWord_3771297
  simp only [CollatzResearch.WordTrace]
  refine ⟨137550501818242530094384145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91700334545495020062922763 137550501818242530094384145)
  ·
    refine ⟨103162876363681897570788109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137550501818242530094384145 103162876363681897570788109)
    ·
      refine ⟨38686078636380711589045541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103162876363681897570788109 38686078636380711589045541)
      ·
        refine ⟨7253639744321383422946039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38686078636380711589045541 7253639744321383422946039)
        ·
          refine ⟨10880459616482075134419059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7253639744321383422946039 10880459616482075134419059)
          ·
            refine ⟨16320689424723112701628589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10880459616482075134419059 16320689424723112701628589)
            ·
              refine ⟨6120258534271167263110721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16320689424723112701628589 6120258534271167263110721)
              ·
                refine ⟨4590193900703375447333041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6120258534271167263110721 4590193900703375447333041)
                ·
                  refine ⟨3442645425527531585499781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4590193900703375447333041 3442645425527531585499781)
                  ·
                    refine ⟨645496017286412172281209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3442645425527531585499781 645496017286412172281209)
                    ·
                      rfl

theorem cell23_3771297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_3771297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771297 prefixEnd_3771297 := by exact prefixLift 3771297
  have htrace : WordTrace (prefixWord ++ tailWord_3771297) baseStart_3771297 baseEnd_3771297 := by
    simpa [prefixWord, tailWord_3771297, baseEnd_3771297] using wordTrace_append hprefix tailTrace_3771297
  have hstable : (prefixWord ++ tailWord_3771297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771297).length < 2 ^ (prefixWord ++ tailWord_3771297).sum := by decide
  have hdescent : baseEnd_3771297 < baseStart_3771297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771320 : List Nat := [2, 1, 2, 1, 2, 4, 3, 1, 1, 3, 3]
def baseStart_3771320 : Nat := 118140960795 + 3771320 * 2 ^ 59
def prefixEnd_3771320 : Nat := 4983230072969 + 3 ^ 40 * 3771320 * 2
def baseEnd_3771320 : Nat := 1936499861914289926856021

theorem tailTrace_3771320 : CollatzResearch.WordTrace tailWord_3771320 prefixEnd_3771320 1936499861914289926856021 := by
  unfold tailWord_3771320
  simp only [CollatzResearch.WordTrace]
  refine ⟨68775670348579602511235707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91700893798106136681647609 68775670348579602511235707)
  ·
    refine ⟨103163505522869403766853561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68775670348579602511235707 103163505522869403766853561)
    ·
      refine ⟨77372629142152052825140171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103163505522869403766853561 77372629142152052825140171)
      ·
        refine ⟨116058943713228079237710257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77372629142152052825140171 116058943713228079237710257)
        ·
          refine ⟨87044207784921059428282693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116058943713228079237710257 87044207784921059428282693)
          ·
            refine ⟨16320788959672698642803005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87044207784921059428282693 16320788959672698642803005)
            ·
              refine ⟨6120295859877261991051127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16320788959672698642803005 6120295859877261991051127)
              ·
                refine ⟨9180443789815892986576691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6120295859877261991051127 9180443789815892986576691)
                ·
                  refine ⟨13770665684723839479865037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9180443789815892986576691 13770665684723839479865037)
                  ·
                    refine ⟨5163999631771439804949389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13770665684723839479865037 5163999631771439804949389)
                    ·
                      refine ⟨1936499861914289926856021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5163999631771439804949389 1936499861914289926856021)
                      ·
                        rfl

theorem cell23_3771320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_3771320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771320 prefixEnd_3771320 := by exact prefixLift 3771320
  have htrace : WordTrace (prefixWord ++ tailWord_3771320) baseStart_3771320 baseEnd_3771320 := by
    simpa [prefixWord, tailWord_3771320, baseEnd_3771320] using wordTrace_append hprefix tailTrace_3771320
  have hstable : (prefixWord ++ tailWord_3771320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771320).length < 2 ^ (prefixWord ++ tailWord_3771320).sum := by decide
  have hdescent : baseEnd_3771320 < baseStart_3771320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771341 : List Nat := [1, 6, 3, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_3771341 : Nat := 118140960795 + 3771341 * 2 ^ 59
def prefixEnd_3771341 : Nat := 4983230072969 + 3 ^ 40 * 3771341 * 2
def baseEnd_3771341 : Nat := 1936510645008034344693425

theorem tailTrace_3771341 : CollatzResearch.WordTrace tailWord_3771341 prefixEnd_3771341 1936510645008034344693425 := by
  unfold tailWord_3771341
  simp only [CollatzResearch.WordTrace]
  refine ⟨137552106630083125608985877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91701404420055417072657251 137552106630083125608985877)
  ·
    refine ⟨6447754998285146512921213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 137552106630083125608985877 6447754998285146512921213)
    ·
      refine ⟨2417908124356929942345455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6447754998285146512921213 2417908124356929942345455)
      ·
        refine ⟨3626862186535394913518183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2417908124356929942345455 3626862186535394913518183)
        ·
          refine ⟨5440293279803092370277275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3626862186535394913518183 5440293279803092370277275)
          ·
            refine ⟨8160439919704638555415913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5440293279803092370277275 8160439919704638555415913)
            ·
              refine ⟨6120329939778478916561935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8160439919704638555415913 6120329939778478916561935)
              ·
                refine ⟨9180494909667718374842903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6120329939778478916561935 9180494909667718374842903)
                ·
                  refine ⟨13770742364501577562264355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9180494909667718374842903 13770742364501577562264355)
                  ·
                    refine ⟨20656113546752366343396533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13770742364501577562264355 20656113546752366343396533)
                    ·
                      refine ⟨1936510645008034344693425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20656113546752366343396533 1936510645008034344693425)
                      ·
                        rfl

theorem cell23_3771341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_3771341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771341 prefixEnd_3771341 := by exact prefixLift 3771341
  have htrace : WordTrace (prefixWord ++ tailWord_3771341) baseStart_3771341 baseEnd_3771341 := by
    simpa [prefixWord, tailWord_3771341, baseEnd_3771341] using wordTrace_append hprefix tailTrace_3771341
  have hstable : (prefixWord ++ tailWord_3771341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771341).length < 2 ^ (prefixWord ++ tailWord_3771341).sum := by decide
  have hdescent : baseEnd_3771341 < baseStart_3771341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771363 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3771363 : Nat := 118140960795 + 3771363 * 2 ^ 59
def prefixEnd_3771363 : Nat := 4983230072969 + 3 ^ 40 * 3771363 * 2
def baseEnd_3771363 : Nat := 1936521941582433258618323

theorem tailTrace_3771363 : CollatzResearch.WordTrace tailWord_3771363 prefixEnd_3771363 1936521941582433258618323 := by
  unfold tailWord_3771363
  simp only [CollatzResearch.WordTrace]
  refine ⟨137552909036003423366286743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91701939357335615577524495 137552909036003423366286743)
  ·
    refine ⟨206329363554005135049430115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137552909036003423366286743 206329363554005135049430115)
    ·
      refine ⟨309494045331007702574145173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206329363554005135049430115 309494045331007702574145173)
      ·
        refine ⟨14507533374890986058163055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 309494045331007702574145173 14507533374890986058163055)
        ·
          refine ⟨21761300062336479087244583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14507533374890986058163055 21761300062336479087244583)
          ·
            refine ⟨32641950093504718630866875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21761300062336479087244583 32641950093504718630866875)
            ·
              refine ⟨48962925140257077946300313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32641950093504718630866875 48962925140257077946300313)
              ·
                refine ⟨36722193855192808459725235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48962925140257077946300313 36722193855192808459725235)
                ·
                  refine ⟨55083290782789212689587853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36722193855192808459725235 55083290782789212689587853)
                  ·
                    refine ⟨20656234043545954758595445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55083290782789212689587853 20656234043545954758595445)
                    ·
                      refine ⟨1936521941582433258618323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20656234043545954758595445 1936521941582433258618323)
                      ·
                        rfl

theorem cell23_3771363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3771363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771363 prefixEnd_3771363 := by exact prefixLift 3771363
  have htrace : WordTrace (prefixWord ++ tailWord_3771363) baseStart_3771363 baseEnd_3771363 := by
    simpa [prefixWord, tailWord_3771363, baseEnd_3771363] using wordTrace_append hprefix tailTrace_3771363
  have hstable : (prefixWord ++ tailWord_3771363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771363).length < 2 ^ (prefixWord ++ tailWord_3771363).sum := by decide
  have hdescent : baseEnd_3771363 < baseStart_3771363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771381 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_3771381 : Nat := 118140960795 + 3771381 * 2 ^ 59
def prefixEnd_3771381 : Nat := 4983230072969 + 3 ^ 40 * 3771381 * 2
def baseEnd_3771381 : Nat := 1936531184234214188193241

theorem tailTrace_3771381 : CollatzResearch.WordTrace tailWord_3771381 prefixEnd_3771381 1936531184234214188193241 := by
  unfold tailWord_3771381
  simp only [CollatzResearch.WordTrace]
  refine ⟨137553565549938212440441997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91702377033292141626961331 137553565549938212440441997)
  ·
    refine ⟨51582587081226829665165749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137553565549938212440441997 51582587081226829665165749)
    ·
      refine ⟨4835867538865015281109289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51582587081226829665165749 4835867538865015281109289)
      ·
        refine ⟨3626900654148761460831967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4835867538865015281109289 3626900654148761460831967)
        ·
          refine ⟨5440350981223142191247951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3626900654148761460831967 5440350981223142191247951)
          ·
            refine ⟨8160526471834713286871927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5440350981223142191247951 8160526471834713286871927)
            ·
              refine ⟨12240789707752069930307891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8160526471834713286871927 12240789707752069930307891)
              ·
                refine ⟨18361184561628104895461837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12240789707752069930307891 18361184561628104895461837)
                ·
                  refine ⟨6885444210610539335798189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18361184561628104895461837 6885444210610539335798189)
                  ·
                    refine ⟨2582041578978952250924321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6885444210610539335798189 2582041578978952250924321)
                    ·
                      refine ⟨1936531184234214188193241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2582041578978952250924321 1936531184234214188193241)
                      ·
                        rfl

theorem cell23_3771381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_3771381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771381 prefixEnd_3771381 := by exact prefixLift 3771381
  have htrace : WordTrace (prefixWord ++ tailWord_3771381) baseStart_3771381 baseEnd_3771381 := by
    simpa [prefixWord, tailWord_3771381, baseEnd_3771381] using wordTrace_append hprefix tailTrace_3771381
  have hstable : (prefixWord ++ tailWord_3771381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771381).length < 2 ^ (prefixWord ++ tailWord_3771381).sum := by decide
  have hdescent : baseEnd_3771381 < baseStart_3771381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771417 : List Nat := [1, 2, 1, 2, 1, 1, 8, 2, 5]
def baseStart_3771417 : Nat := 118140960795 + 3771417 * 2 ^ 59
def prefixEnd_3771417 : Nat := 4983230072969 + 3 ^ 40 * 3771417 * 2
def baseEnd_3771417 : Nat := 215172185504197338593675

theorem tailTrace_3771417 : CollatzResearch.WordTrace tailWord_3771417 prefixEnd_3771417 215172185504197338593675 := by
  unfold tailWord_3771417
  simp only [CollatzResearch.WordTrace]
  refine ⟨137554878577807790588752505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91703252385205193725835003 137554878577807790588752505)
  ·
    refine ⟨103166158933355842941564379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137554878577807790588752505 103166158933355842941564379)
    ·
      refine ⟨154749238400033764412346569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103166158933355842941564379 154749238400033764412346569)
      ·
        refine ⟨116061928800025323309259927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154749238400033764412346569 116061928800025323309259927)
        ·
          refine ⟨174092893200037984963889891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116061928800025323309259927 174092893200037984963889891)
          ·
            refine ⟨261139339800056977445834837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174092893200037984963889891 261139339800056977445834837)
            ·
              refine ⟨3060226638281917704443377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 261139339800056977445834837 3060226638281917704443377)
              ·
                refine ⟨2295169978711438278332533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3060226638281917704443377 2295169978711438278332533)
                ·
                  refine ⟨215172185504197338593675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2295169978711438278332533 215172185504197338593675)
                  ·
                    rfl

theorem cell23_3771417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 5].length) (baseStart_3771417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771417 prefixEnd_3771417 := by exact prefixLift 3771417
  have htrace : WordTrace (prefixWord ++ tailWord_3771417) baseStart_3771417 baseEnd_3771417 := by
    simpa [prefixWord, tailWord_3771417, baseEnd_3771417] using wordTrace_append hprefix tailTrace_3771417
  have hstable : (prefixWord ++ tailWord_3771417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771417).length < 2 ^ (prefixWord ++ tailWord_3771417).sum := by decide
  have hdescent : baseEnd_3771417 < baseStart_3771417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771477 : List Nat := [1, 3, 2, 2, 1, 2, 4, 1, 3, 4]
def baseStart_3771477 : Nat := 118140960795 + 3771477 * 2 ^ 59
def prefixEnd_3771477 : Nat := 4983230072969 + 3 ^ 40 * 3771477 * 2
def baseEnd_3771477 : Nat := 645526826125681937530933

theorem tailTrace_3771477 : CollatzResearch.WordTrace tailWord_3771477 prefixEnd_3771477 645526826125681937530933 := by
  unfold tailWord_3771477
  simp only [CollatzResearch.WordTrace]
  refine ⟨137557066957590420835936685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91704711305060280557291123 137557066957590420835936685)
  ·
    refine ⟨51583900109096407813476257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137557066957590420835936685 51583900109096407813476257)
    ·
      refine ⟨38687925081822305860107193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51583900109096407813476257 38687925081822305860107193)
      ·
        refine ⟨29015943811366729395080395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38687925081822305860107193 29015943811366729395080395)
        ·
          refine ⟨43523915717050094092620593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29015943811366729395080395 43523915717050094092620593)
          ·
            refine ⟨32642936787787570569465445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43523915717050094092620593 32642936787787570569465445)
            ·
              refine ⟨6120550647710169481774771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32642936787787570569465445 6120550647710169481774771)
              ·
                refine ⟨9180825971565254222662157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6120550647710169481774771 9180825971565254222662157)
                ·
                  refine ⟨3442809739336970333498309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9180825971565254222662157 3442809739336970333498309)
                  ·
                    refine ⟨645526826125681937530933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3442809739336970333498309 645526826125681937530933)
                    ·
                      rfl

theorem cell23_3771477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_3771477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771477 prefixEnd_3771477 := by exact prefixLift 3771477
  have htrace : WordTrace (prefixWord ++ tailWord_3771477) baseStart_3771477 baseEnd_3771477 := by
    simpa [prefixWord, tailWord_3771477, baseEnd_3771477] using wordTrace_append hprefix tailTrace_3771477
  have hstable : (prefixWord ++ tailWord_3771477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771477).length < 2 ^ (prefixWord ++ tailWord_3771477).sum := by decide
  have hdescent : baseEnd_3771477 < baseStart_3771477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771500 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 3]
def baseStart_3771500 : Nat := 118140960795 + 3771500 * 2 ^ 59
def prefixEnd_3771500 : Nat := 4983230072969 + 3 ^ 40 * 3771500 * 2
def baseEnd_3771500 : Nat := 1936592288432099222605193

theorem tailTrace_3771500 : CollatzResearch.WordTrace tailWord_3771500 prefixEnd_3771500 1936592288432099222605193 := by
  unfold tailWord_3771500
  simp only [CollatzResearch.WordTrace]
  refine ⟨68778952918253547882011977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91705270557671397176015969 68778952918253547882011977)
  ·
    refine ⟨51584214688690160911508983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68778952918253547882011977 51584214688690160911508983)
    ·
      refine ⟨77376322033035241367263475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51584214688690160911508983 77376322033035241367263475)
      ·
        refine ⟨116064483049552862050895213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77376322033035241367263475 116064483049552862050895213)
        ·
          refine ⟨43524181143582323269085705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116064483049552862050895213 43524181143582323269085705)
          ·
            refine ⟨32643135857686742451814279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43524181143582323269085705 32643135857686742451814279)
            ·
              refine ⟨48964703786530113677721419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32643135857686742451814279 48964703786530113677721419)
              ·
                refine ⟨73447055679795170516582129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48964703786530113677721419 73447055679795170516582129)
                ·
                  refine ⟨55085291759846377887436597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73447055679795170516582129 55085291759846377887436597)
                  ·
                    refine ⟨5164246102485597926947181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55085291759846377887436597 5164246102485597926947181)
                    ·
                      refine ⟨1936592288432099222605193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5164246102485597926947181 1936592288432099222605193)
                      ·
                        rfl

theorem cell23_3771500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_3771500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771500 prefixEnd_3771500 := by exact prefixLift 3771500
  have htrace : WordTrace (prefixWord ++ tailWord_3771500) baseStart_3771500 baseEnd_3771500 := by
    simpa [prefixWord, tailWord_3771500, baseEnd_3771500] using wordTrace_append hprefix tailTrace_3771500
  have hstable : (prefixWord ++ tailWord_3771500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771500).length < 2 ^ (prefixWord ++ tailWord_3771500).sum := by decide
  have hdescent : baseEnd_3771500 < baseStart_3771500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771518 : List Nat := [4, 2, 4, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3771518 : Nat := 118140960795 + 3771518 * 2 ^ 59
def prefixEnd_3771518 : Nat := 4983230072969 + 3 ^ 40 * 3771518 * 2
def baseEnd_3771518 : Nat := 1936601531083880152180111

theorem tailTrace_3771518 : CollatzResearch.WordTrace tailWord_3771518 prefixEnd_3771518 1936601531083880152180111 := by
  unfold tailWord_3771518
  simp only [CollatzResearch.WordTrace]
  refine ⟨17194820293805235604772401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91705708233627923225452805 17194820293805235604772401)
  ·
    refine ⟨12896115220353926703579301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17194820293805235604772401 12896115220353926703579301)
    ·
      refine ⟨2418021603816361256921119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12896115220353926703579301 2418021603816361256921119)
      ·
        refine ⟨3627032405724541885381679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2418021603816361256921119 3627032405724541885381679)
        ·
          refine ⟨5440548608586812828072519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3627032405724541885381679 5440548608586812828072519)
          ·
            refine ⟨8160822912880219242108779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5440548608586812828072519 8160822912880219242108779)
            ·
              refine ⟨12241234369320328863163169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8160822912880219242108779 12241234369320328863163169)
              ·
                refine ⟨9180925776990246647372377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12241234369320328863163169 9180925776990246647372377)
                ·
                  refine ⟨6885694332742684985529283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9180925776990246647372377 6885694332742684985529283)
                  ·
                    refine ⟨10328541499114027478293925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6885694332742684985529283 10328541499114027478293925)
                    ·
                      refine ⟨1936601531083880152180111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10328541499114027478293925 1936601531083880152180111)
                      ·
                        rfl

theorem cell23_3771518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3771518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771518 prefixEnd_3771518 := by exact prefixLift 3771518
  have htrace : WordTrace (prefixWord ++ tailWord_3771518) baseStart_3771518 baseEnd_3771518 := by
    simpa [prefixWord, tailWord_3771518, baseEnd_3771518] using wordTrace_append hprefix tailTrace_3771518
  have hstable : (prefixWord ++ tailWord_3771518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771518).length < 2 ^ (prefixWord ++ tailWord_3771518).sum := by decide
  have hdescent : baseEnd_3771518 < baseStart_3771518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771528 : List Nat := [2, 1, 3, 4, 2, 1, 3, 2, 1, 4]
def baseStart_3771528 : Nat := 118140960795 + 3771528 * 2 ^ 59
def prefixEnd_3771528 : Nat := 4983230072969 + 3 ^ 40 * 3771528 * 2
def baseEnd_3771528 : Nat := 645535555296808371018355

theorem tailTrace_3771528 : CollatzResearch.WordTrace tailWord_3771528 prefixEnd_3771528 645535555296808371018355 := by
  unfold tailWord_3771528
  simp only [CollatzResearch.WordTrace]
  refine ⟨68779463540202828273021619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91705951386937104364028825 68779463540202828273021619)
  ·
    refine ⟨103169195310304242409532429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68779463540202828273021619 103169195310304242409532429)
    ·
      refine ⟨38688448241364090903574661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103169195310304242409532429 38688448241364090903574661)
      ·
        refine ⟨7254084045255767044420249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38688448241364090903574661 7254084045255767044420249)
        ·
          refine ⟨5440563033941825283315187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7254084045255767044420249 5440563033941825283315187)
          ·
            refine ⟨8160844550912737924972781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5440563033941825283315187 8160844550912737924972781)
            ·
              refine ⟨3060316706592276721864793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8160844550912737924972781 3060316706592276721864793)
              ·
                refine ⟨2295237529944207541398595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3060316706592276721864793 2295237529944207541398595)
                ·
                  refine ⟨3442856294916311312097893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2295237529944207541398595 3442856294916311312097893)
                  ·
                    refine ⟨645535555296808371018355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3442856294916311312097893 645535555296808371018355)
                    ·
                      rfl

theorem cell23_3771528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_3771528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771528 prefixEnd_3771528 := by exact prefixLift 3771528
  have htrace : WordTrace (prefixWord ++ tailWord_3771528) baseStart_3771528 baseEnd_3771528 := by
    simpa [prefixWord, tailWord_3771528, baseEnd_3771528] using wordTrace_append hprefix tailTrace_3771528
  have hstable : (prefixWord ++ tailWord_3771528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771528).length < 2 ^ (prefixWord ++ tailWord_3771528).sum := by decide
  have hdescent : baseEnd_3771528 < baseStart_3771528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771554 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_3771554 : Nat := 118140960795 + 3771554 * 2 ^ 59
def prefixEnd_3771554 : Nat := 4983230072969 + 3 ^ 40 * 3771554 * 2
def baseEnd_3771554 : Nat := 645540005462480670443315

theorem tailTrace_3771554 : CollatzResearch.WordTrace tailWord_3771554 prefixEnd_3771554 645540005462480670443315 := by
  unfold tailWord_3771554
  simp only [CollatzResearch.WordTrace]
  refine ⟨34389968844577865746622429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91706583585540975324326477 34389968844577865746622429)
  ·
    refine ⟨12896238316716699654983411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34389968844577865746622429 12896238316716699654983411)
    ·
      refine ⟨19344357475075049482475117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12896238316716699654983411 19344357475075049482475117)
      ·
        refine ⟨7254134053153143555928169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19344357475075049482475117 7254134053153143555928169)
        ·
          refine ⟨5440600539864857666946127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7254134053153143555928169 5440600539864857666946127)
          ·
            refine ⟨8160900809797286500419191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5440600539864857666946127 8160900809797286500419191)
            ·
              refine ⟨12241351214695929750628787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8160900809797286500419191 12241351214695929750628787)
              ·
                refine ⟨18362026822043894625943181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12241351214695929750628787 18362026822043894625943181)
                ·
                  refine ⟨6885760058266460484728693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18362026822043894625943181 6885760058266460484728693)
                  ·
                    refine ⟨645540005462480670443315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6885760058266460484728693 645540005462480670443315)
                    ·
                      rfl

theorem cell23_3771554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_3771554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771554 prefixEnd_3771554 := by exact prefixLift 3771554
  have htrace : WordTrace (prefixWord ++ tailWord_3771554) baseStart_3771554 baseEnd_3771554 := by
    simpa [prefixWord, tailWord_3771554, baseEnd_3771554] using wordTrace_append hprefix tailTrace_3771554
  have hstable : (prefixWord ++ tailWord_3771554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771554).length < 2 ^ (prefixWord ++ tailWord_3771554).sum := by decide
  have hdescent : baseEnd_3771554 < baseStart_3771554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771557 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 3, 1, 4]
def baseStart_3771557 : Nat := 118140960795 + 3771557 * 2 ^ 59
def prefixEnd_3771557 : Nat := 4983230072969 + 3 ^ 40 * 3771557 * 2
def baseEnd_3771557 : Nat := 1936621556829405499592431

theorem tailTrace_3771557 : CollatzResearch.WordTrace tailWord_3771557 prefixEnd_3771557 1936621556829405499592431 := by
  unfold tailWord_3771557
  simp only [CollatzResearch.WordTrace]
  refine ⟨137559984797300594498848925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91706656531533729665899283 137559984797300594498848925)
  ·
    refine ⟨51584994298987722937068347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137559984797300594498848925 51584994298987722937068347)
    ·
      refine ⟨77377491448481584405602521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51584994298987722937068347 77377491448481584405602521)
      ·
        refine ⟨58033118586361188304201891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77377491448481584405602521 58033118586361188304201891)
        ·
          refine ⟨87049677879541782456302837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58033118586361188304201891 87049677879541782456302837)
          ·
            refine ⟨8160907301207042105278391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87049677879541782456302837 8160907301207042105278391)
            ·
              refine ⟨12241360951810563157917587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8160907301207042105278391 12241360951810563157917587)
              ·
                refine ⟨18362041427715844736876381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12241360951810563157917587 18362041427715844736876381)
                ·
                  refine ⟨6885765535393441776328643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18362041427715844736876381 6885765535393441776328643)
                  ·
                    refine ⟨10328648303090162664492965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6885765535393441776328643 10328648303090162664492965)
                    ·
                      refine ⟨1936621556829405499592431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10328648303090162664492965 1936621556829405499592431)
                      ·
                        rfl

theorem cell23_3771557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_3771557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771557 prefixEnd_3771557 := by exact prefixLift 3771557
  have htrace : WordTrace (prefixWord ++ tailWord_3771557) baseStart_3771557 baseEnd_3771557 := by
    simpa [prefixWord, tailWord_3771557, baseEnd_3771557] using wordTrace_append hprefix tailTrace_3771557
  have hstable : (prefixWord ++ tailWord_3771557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771557).length < 2 ^ (prefixWord ++ tailWord_3771557).sum := by decide
  have hdescent : baseEnd_3771557 < baseStart_3771557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771577 : List Nat := [1, 2, 1, 4, 1, 3, 3, 1, 1, 1, 5]
def baseStart_3771577 : Nat := 118140960795 + 3771577 * 2 ^ 59
def prefixEnd_3771577 : Nat := 4983230072969 + 3 ^ 40 * 3771577 * 2
def baseEnd_3771577 : Nat := 1936631826442495421342339

theorem tailTrace_3771577 : CollatzResearch.WordTrace tailWord_3771577 prefixEnd_3771577 1936631826442495421342339 := by
  unfold tailWord_3771577
  simp only [CollatzResearch.WordTrace]
  refine ⟨137560714257228137914576985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91707142838152091943051323 137560714257228137914576985)
  ·
    refine ⟨103170535692921103435932739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137560714257228137914576985 103170535692921103435932739)
    ·
      refine ⟨154755803539381655153899109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103170535692921103435932739 154755803539381655153899109)
      ·
        refine ⟨29016713163634060341356083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154755803539381655153899109 29016713163634060341356083)
        ·
          refine ⟨43525069745451090512034125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29016713163634060341356083 43525069745451090512034125)
          ·
            refine ⟨16321901154544158942012797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43525069745451090512034125 16321901154544158942012797)
            ·
              refine ⟨6120712932954059603254799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16321901154544158942012797 6120712932954059603254799)
              ·
                refine ⟨9181069399431089404882199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6120712932954059603254799 9181069399431089404882199)
                ·
                  refine ⟨13771604099146634107323299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9181069399431089404882199 13771604099146634107323299)
                  ·
                    refine ⟨20657406148719951160984949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13771604099146634107323299 20657406148719951160984949)
                    ·
                      refine ⟨1936631826442495421342339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20657406148719951160984949 1936631826442495421342339)
                      ·
                        rfl

theorem cell23_3771577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_3771577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771577 prefixEnd_3771577 := by exact prefixLift 3771577
  have htrace : WordTrace (prefixWord ++ tailWord_3771577) baseStart_3771577 baseEnd_3771577 := by
    simpa [prefixWord, tailWord_3771577, baseEnd_3771577] using wordTrace_append hprefix tailTrace_3771577
  have hstable : (prefixWord ++ tailWord_3771577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771577).length < 2 ^ (prefixWord ++ tailWord_3771577).sum := by decide
  have hdescent : baseEnd_3771577 < baseStart_3771577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771580 : List Nat := [2, 2, 2, 3, 2, 12]
def baseStart_3771580 : Nat := 118140960795 + 3771580 * 2 ^ 59
def prefixEnd_3771580 : Nat := 4983230072969 + 3 ^ 40 * 3771580 * 2
def baseEnd_3771580 : Nat := 7969684637384604566275

theorem tailTrace_3771580 : CollatzResearch.WordTrace tailWord_3771580 prefixEnd_3771580 7969684637384604566275 := by
  unfold tailWord_3771580
  simp only [CollatzResearch.WordTrace]
  refine ⟨68780411838108634713468097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91707215784144846284624129 68780411838108634713468097)
  ·
    refine ⟨51585308878581476035101073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68780411838108634713468097 51585308878581476035101073)
    ·
      refine ⟨38688981658936107026325805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51585308878581476035101073 38688981658936107026325805)
      ·
        refine ⟨14508368122101040134872177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38688981658936107026325805 14508368122101040134872177)
        ·
          refine ⟨10881276091575780101154133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14508368122101040134872177 10881276091575780101154133)
          ·
            refine ⟨7969684637384604566275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10881276091575780101154133 7969684637384604566275)
            ·
              rfl

theorem cell23_3771580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 12].length) (baseStart_3771580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771580 prefixEnd_3771580 := by exact prefixLift 3771580
  have htrace : WordTrace (prefixWord ++ tailWord_3771580) baseStart_3771580 baseEnd_3771580 := by
    simpa [prefixWord, tailWord_3771580, baseEnd_3771580] using wordTrace_append hprefix tailTrace_3771580
  have hstable : (prefixWord ++ tailWord_3771580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771580).length < 2 ^ (prefixWord ++ tailWord_3771580).sum := by decide
  have hdescent : baseEnd_3771580 < baseStart_3771580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771585 : List Nat := [1, 2, 6, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_3771585 : Nat := 118140960795 + 3771585 * 2 ^ 59
def prefixEnd_3771585 : Nat := 4983230072969 + 3 ^ 40 * 3771585 * 2
def baseEnd_3771585 : Nat := 1936635934287731390042303

theorem tailTrace_3771585 : CollatzResearch.WordTrace tailWord_3771585 prefixEnd_3771585 1936635934287731390042303 := by
  unfold tailWord_3771585
  simp only [CollatzResearch.WordTrace]
  refine ⟨137561006041199155280868209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91707337360799436853912139 137561006041199155280868209)
  ·
    refine ⟨103170754530899366460651157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137561006041199155280868209 103170754530899366460651157)
    ·
      refine ⟨4836129118635907802843023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103170754530899366460651157 4836129118635907802843023)
      ·
        refine ⟨7254193677953861704264535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4836129118635907802843023 7254193677953861704264535)
        ·
          refine ⟨10881290516930792556396803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7254193677953861704264535 10881290516930792556396803)
          ·
            refine ⟨16321935775396188834595205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10881290516930792556396803 16321935775396188834595205)
            ·
              refine ⟨3060362957886785406486601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16321935775396188834595205 3060362957886785406486601)
              ·
                refine ⟨2295272218415089054864951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3060362957886785406486601 2295272218415089054864951)
                ·
                  refine ⟨3442908327622633582297427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2295272218415089054864951 3442908327622633582297427)
                  ·
                    refine ⟨5164362491433950373446141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3442908327622633582297427 5164362491433950373446141)
                    ·
                      refine ⟨1936635934287731390042303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5164362491433950373446141 1936635934287731390042303)
                      ·
                        rfl

theorem cell23_3771585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_3771585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771585 prefixEnd_3771585 := by exact prefixLift 3771585
  have htrace : WordTrace (prefixWord ++ tailWord_3771585) baseStart_3771585 baseEnd_3771585 := by
    simpa [prefixWord, tailWord_3771585, baseEnd_3771585] using wordTrace_append hprefix tailTrace_3771585
  have hstable : (prefixWord ++ tailWord_3771585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771585).length < 2 ^ (prefixWord ++ tailWord_3771585).sum := by decide
  have hdescent : baseEnd_3771585 < baseStart_3771585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771607 : List Nat := [1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 3]
def baseStart_3771607 : Nat := 118140960795 + 3771607 * 2 ^ 59
def prefixEnd_3771607 : Nat := 4983230072969 + 3 ^ 40 * 3771607 * 2
def baseEnd_3771607 : Nat := 1936647230862130303967201

theorem tailTrace_3771607 : CollatzResearch.WordTrace tailWord_3771607 prefixEnd_3771607 1936647230862130303967201 := by
  unfold tailWord_3771607
  simp only [CollatzResearch.WordTrace]
  refine ⟨137561808447119453038169075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91707872298079635358779383 137561808447119453038169075)
  ·
    refine ⟨206342712670679179557253613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137561808447119453038169075 206342712670679179557253613)
    ·
      refine ⟨77378517251504692333970105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206342712670679179557253613 77378517251504692333970105)
      ·
        refine ⟨58033887938628519250477579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77378517251504692333970105 58033887938628519250477579)
        ·
          refine ⟨87050831907942778875716369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58033887938628519250477579 87050831907942778875716369)
          ·
            refine ⟨65288123930957084156787277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87050831907942778875716369 65288123930957084156787277)
            ·
              refine ⟨24483046474108906558795229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65288123930957084156787277 24483046474108906558795229)
              ·
                refine ⟨9181142427790839959548211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24483046474108906558795229 9181142427790839959548211)
                ·
                  refine ⟨13771713641686259939322317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9181142427790839959548211 13771713641686259939322317)
                  ·
                    refine ⟨5164392615632347477245869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13771713641686259939322317 5164392615632347477245869)
                    ·
                      refine ⟨1936647230862130303967201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5164392615632347477245869 1936647230862130303967201)
                      ·
                        rfl

theorem cell23_3771607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_3771607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771607 prefixEnd_3771607 := by exact prefixLift 3771607
  have htrace : WordTrace (prefixWord ++ tailWord_3771607) baseStart_3771607 baseEnd_3771607 := by
    simpa [prefixWord, tailWord_3771607, baseEnd_3771607] using wordTrace_append hprefix tailTrace_3771607
  have hstable : (prefixWord ++ tailWord_3771607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771607).length < 2 ^ (prefixWord ++ tailWord_3771607).sum := by decide
  have hdescent : baseEnd_3771607 < baseStart_3771607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771610 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 4, 7]
def baseStart_3771610 : Nat := 118140960795 + 3771610 * 2 ^ 59
def prefixEnd_3771610 : Nat := 4983230072969 + 3 ^ 40 * 3771610 * 2
def baseEnd_3771610 : Nat := 645549590434697930743229

theorem tailTrace_3771610 : CollatzResearch.WordTrace tailWord_3771610 prefixEnd_3771610 645549590434697930743229 := by
  unfold tailWord_3771610
  simp only [CollatzResearch.WordTrace]
  refine ⟨34390479466527146137632071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91707945244072389700352189 34390479466527146137632071)
  ·
    refine ⟨51585719199790719206448107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34390479466527146137632071 51585719199790719206448107)
    ·
      refine ⟨77378578799686078809672161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51585719199790719206448107 77378578799686078809672161)
      ·
        refine ⟨58033934099764559107254121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77378578799686078809672161 58033934099764559107254121)
        ·
          refine ⟨43525450574823419330440591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58033934099764559107254121 43525450574823419330440591)
          ·
            refine ⟨65288175862235128995660887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43525450574823419330440591 65288175862235128995660887)
            ·
              refine ⟨97932263793352693493491331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65288175862235128995660887 97932263793352693493491331)
              ·
                refine ⟨146898395690029040240236997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97932263793352693493491331 146898395690029040240236997)
                ·
                  refine ⟨27543449191880445045044437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146898395690029040240236997 27543449191880445045044437)
                  ·
                    refine ⟨645549590434697930743229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27543449191880445045044437 645549590434697930743229)
                    ·
                      rfl

theorem cell23_3771610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_3771610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771610 prefixEnd_3771610 := by exact prefixLift 3771610
  have htrace : WordTrace (prefixWord ++ tailWord_3771610) baseStart_3771610 baseEnd_3771610 := by
    simpa [prefixWord, tailWord_3771610, baseEnd_3771610] using wordTrace_append hprefix tailTrace_3771610
  have hstable : (prefixWord ++ tailWord_3771610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771610).length < 2 ^ (prefixWord ++ tailWord_3771610).sum := by decide
  have hdescent : baseEnd_3771610 < baseStart_3771610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771624 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_3771624 : Nat := 118140960795 + 3771624 * 2 ^ 59
def prefixEnd_3771624 : Nat := 4983230072969 + 3 ^ 40 * 3771624 * 2
def baseEnd_3771624 : Nat := 1936655960033256737454623

theorem tailTrace_3771624 : CollatzResearch.WordTrace tailWord_3771624 prefixEnd_3771624 1936655960033256737454623 := by
  unfold tailWord_3771624
  simp only [CollatzResearch.WordTrace]
  refine ⟨68781214244028932470768963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91708285658705243294358617 68781214244028932470768963)
  ·
    refine ⟨103171821366043398706153445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68781214244028932470768963 103171821366043398706153445)
    ·
      refine ⟨19344716506133137257403771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103171821366043398706153445 19344716506133137257403771)
      ·
        refine ⟨29017074759199705886105657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19344716506133137257403771 29017074759199705886105657)
        ·
          refine ⟨21762806069399779414579243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29017074759199705886105657 21762806069399779414579243)
          ·
            refine ⟨32644209104099669121868865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21762806069399779414579243 32644209104099669121868865)
            ·
              refine ⟨24483156828074751841401649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32644209104099669121868865 24483156828074751841401649)
              ·
                refine ⟨18362367621056063881051237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24483156828074751841401649 18362367621056063881051237)
                ·
                  refine ⟨3442943928948011977697107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18362367621056063881051237 3442943928948011977697107)
                  ·
                    refine ⟨5164415893422017966545661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3442943928948011977697107 5164415893422017966545661)
                    ·
                      refine ⟨1936655960033256737454623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5164415893422017966545661 1936655960033256737454623)
                      ·
                        rfl

theorem cell23_3771624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_3771624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771624 prefixEnd_3771624 := by exact prefixLift 3771624
  have htrace : WordTrace (prefixWord ++ tailWord_3771624) baseStart_3771624 baseEnd_3771624 := by
    simpa [prefixWord, tailWord_3771624, baseEnd_3771624] using wordTrace_append hprefix tailTrace_3771624
  have hstable : (prefixWord ++ tailWord_3771624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771624).length < 2 ^ (prefixWord ++ tailWord_3771624).sum := by decide
  have hdescent : baseEnd_3771624 < baseStart_3771624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771737 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 1, 3, 4]
def baseStart_3771737 : Nat := 118140960795 + 3771737 * 2 ^ 59
def prefixEnd_3771737 : Nat := 4983230072969 + 3 ^ 40 * 3771737 * 2
def baseEnd_3771737 : Nat := 1936713983347214795341603

theorem tailTrace_3771737 : CollatzResearch.WordTrace tailWord_3771737 prefixEnd_3771737 1936713983347214795341603 := by
  unfold tailWord_3771737
  simp only [CollatzResearch.WordTrace]
  refine ⟨137566549936648485240401465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91711033291098990160267643 137566549936648485240401465)
  ·
    refine ⟨103174912452486363930301099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137566549936648485240401465 103174912452486363930301099)
    ·
      refine ⟨154762368678729545895451649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103174912452486363930301099 154762368678729545895451649)
      ·
        refine ⟨116071776509047159421588737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154762368678729545895451649 116071776509047159421588737)
        ·
          refine ⟨87053832381785369566191553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116071776509047159421588737 87053832381785369566191553)
          ·
            refine ⟨65290374286339027174643665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87053832381785369566191553 65290374286339027174643665)
            ·
              refine ⟨48967780714754270380982749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65290374286339027174643665 48967780714754270380982749)
              ·
                refine ⟨18362917768032851392868531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48967780714754270380982749 18362917768032851392868531)
                ·
                  refine ⟨27544376652049277089302797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18362917768032851392868531 27544376652049277089302797)
                  ·
                    refine ⟨10329141244518478908488549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27544376652049277089302797 10329141244518478908488549)
                    ·
                      refine ⟨1936713983347214795341603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10329141244518478908488549 1936713983347214795341603)
                      ·
                        rfl

theorem cell23_3771737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_3771737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771737 prefixEnd_3771737 := by exact prefixLift 3771737
  have htrace : WordTrace (prefixWord ++ tailWord_3771737) baseStart_3771737 baseEnd_3771737 := by
    simpa [prefixWord, tailWord_3771737, baseEnd_3771737] using wordTrace_append hprefix tailTrace_3771737
  have hstable : (prefixWord ++ tailWord_3771737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771737).length < 2 ^ (prefixWord ++ tailWord_3771737).sum := by decide
  have hdescent : baseEnd_3771737 < baseStart_3771737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771854 : List Nat := [4, 1, 1, 1, 2, 1, 2, 4, 1, 6]
def baseStart_3771854 : Nat := 118140960795 + 3771854 * 2 ^ 59
def prefixEnd_3771854 : Nat := 4983230072969 + 3 ^ 40 * 3771854 * 2
def baseEnd_3771854 : Nat := 645591353527930279192855

theorem tailTrace_3771854 : CollatzResearch.WordTrace tailWord_3771854 prefixEnd_3771854 645591353527930279192855 := by
  unfold tailWord_3771854
  simp only [CollatzResearch.WordTrace]
  refine ⟨17196352159653076777801327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91713878184816409481607077 17196352159653076777801327)
  ·
    refine ⟨25794528239479615166701991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17196352159653076777801327 25794528239479615166701991)
    ·
      refine ⟨38691792359219422750052987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25794528239479615166701991 38691792359219422750052987)
      ·
        refine ⟨58037688538829134125079481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38691792359219422750052987 58037688538829134125079481)
        ·
          refine ⟨43528266404121850593809611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58037688538829134125079481 43528266404121850593809611)
          ·
            refine ⟨65292399606182775890714417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43528266404121850593809611 65292399606182775890714417)
            ·
              refine ⟨48969299704637081918035813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65292399606182775890714417 48969299704637081918035813)
              ·
                refine ⟨9181743694619452859631715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48969299704637081918035813 9181743694619452859631715)
                ·
                  refine ⟨13772615541929179289447573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9181743694619452859631715 13772615541929179289447573)
                  ·
                    refine ⟨645591353527930279192855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13772615541929179289447573 645591353527930279192855)
                    ·
                      rfl

theorem cell23_3771854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_3771854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771854 prefixEnd_3771854 := by exact prefixLift 3771854
  have htrace : WordTrace (prefixWord ++ tailWord_3771854) baseStart_3771854 baseEnd_3771854 := by
    simpa [prefixWord, tailWord_3771854, baseEnd_3771854] using wordTrace_append hprefix tailTrace_3771854
  have hstable : (prefixWord ++ tailWord_3771854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771854).length < 2 ^ (prefixWord ++ tailWord_3771854).sum := by decide
  have hdescent : baseEnd_3771854 < baseStart_3771854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771861 : List Nat := [1, 3, 2, 3, 1, 1, 1, 5, 1, 1, 4]
def baseStart_3771861 : Nat := 118140960795 + 3771861 * 2 ^ 59
def prefixEnd_3771861 : Nat := 4983230072969 + 3 ^ 40 * 3771861 * 2
def baseEnd_3771861 : Nat := 1936777654948372310191033

theorem tailTrace_3771861 : CollatzResearch.WordTrace tailWord_3771861 prefixEnd_3771861 1936777654948372310191033 := by
  unfold tailWord_3771861
  simp only [CollatzResearch.WordTrace]
  refine ⟨137571072588199254417915437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91714048392132836278610291 137571072588199254417915437)
  ·
    refine ⟨51589152220574720406718289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137571072588199254417915437 51589152220574720406718289)
    ·
      refine ⟨38691864165431040305038717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51589152220574720406718289 38691864165431040305038717)
      ·
        refine ⟨14509449062036640114389519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38691864165431040305038717 14509449062036640114389519)
        ·
          refine ⟨21764173593054960171584279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14509449062036640114389519 21764173593054960171584279)
          ·
            refine ⟨32646260389582440257376419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21764173593054960171584279 32646260389582440257376419)
            ·
              refine ⟨48969390584373660386064629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32646260389582440257376419 48969390584373660386064629)
              ·
                refine ⟨4590880367285030661193559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48969390584373660386064629 4590880367285030661193559)
                ·
                  refine ⟨6886320550927545991790339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4590880367285030661193559 6886320550927545991790339)
                  ·
                    refine ⟨10329480826391318987685509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6886320550927545991790339 10329480826391318987685509)
                    ·
                      refine ⟨1936777654948372310191033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10329480826391318987685509 1936777654948372310191033)
                      ·
                        rfl

theorem cell23_3771861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_3771861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771861 prefixEnd_3771861 := by exact prefixLift 3771861
  have htrace : WordTrace (prefixWord ++ tailWord_3771861) baseStart_3771861 baseEnd_3771861 := by
    simpa [prefixWord, tailWord_3771861, baseEnd_3771861] using wordTrace_append hprefix tailTrace_3771861
  have hstable : (prefixWord ++ tailWord_3771861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771861).length < 2 ^ (prefixWord ++ tailWord_3771861).sum := by decide
  have hdescent : baseEnd_3771861 < baseStart_3771861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771864 : List Nat := [2, 1, 2, 2, 2, 1, 3, 3, 1, 1, 5]
def baseStart_3771864 : Nat := 118140960795 + 3771864 * 2 ^ 59
def prefixEnd_3771864 : Nat := 4983230072969 + 3 ^ 40 * 3771864 * 2
def baseEnd_3771864 : Nat := 1936779195390335798453519

theorem tailTrace_3771864 : CollatzResearch.WordTrace tailWord_3771864 prefixEnd_3771864 1936779195390335798453519 := by
  unfold tailWord_3771864
  simp only [CollatzResearch.WordTrace]
  refine ⟨68785591003594192965137323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91714121338125590620183097 68785591003594192965137323)
  ·
    refine ⟨103178386505391289447705985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68785591003594192965137323 103178386505391289447705985)
    ·
      refine ⟨77383789879043467085779489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103178386505391289447705985 77383789879043467085779489)
      ·
        refine ⟨58037842409282600314334617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77383789879043467085779489 58037842409282600314334617)
        ·
          refine ⟨43528381806961950235750963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58037842409282600314334617 43528381806961950235750963)
          ·
            refine ⟨65292572710442925353626445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43528381806961950235750963 65292572710442925353626445)
            ·
              refine ⟨24484714766416097007609917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65292572710442925353626445 24484714766416097007609917)
              ·
                refine ⟨9181768037406036377853719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24484714766416097007609917 9181768037406036377853719)
                ·
                  refine ⟨13772652056109054566780579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9181768037406036377853719 13772652056109054566780579)
                  ·
                    refine ⟨20658978084163581850170869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13772652056109054566780579 20658978084163581850170869)
                    ·
                      refine ⟨1936779195390335798453519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20658978084163581850170869 1936779195390335798453519)
                      ·
                        rfl

theorem cell23_3771864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_3771864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771864 prefixEnd_3771864 := by exact prefixLift 3771864
  have htrace : WordTrace (prefixWord ++ tailWord_3771864) baseStart_3771864 baseEnd_3771864 := by
    simpa [prefixWord, tailWord_3771864, baseEnd_3771864] using wordTrace_append hprefix tailTrace_3771864
  have hstable : (prefixWord ++ tailWord_3771864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771864).length < 2 ^ (prefixWord ++ tailWord_3771864).sum := by decide
  have hdescent : baseEnd_3771864 < baseStart_3771864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771871 : List Nat := [1, 1, 2, 3, 3, 1, 2, 4, 2, 4]
def baseStart_3771871 : Nat := 118140960795 + 3771871 * 2 ^ 59
def prefixEnd_3771871 : Nat := 4983230072969 + 3 ^ 40 * 3771871 * 2
def baseEnd_3771871 : Nat := 645594263251639090355329

theorem tailTrace_3771871 : CollatzResearch.WordTrace tailWord_3771871 prefixEnd_3771871 645594263251639090355329 := by
  unfold tailWord_3771871
  simp only [CollatzResearch.WordTrace]
  refine ⟨137571437318163026125779467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91714291545442017417186311 137571437318163026125779467)
  ·
    refine ⟨206357155977244539188669201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137571437318163026125779467 206357155977244539188669201)
    ·
      refine ⟨154767866982933404391501901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206357155977244539188669201 154767866982933404391501901)
      ·
        refine ⟨58037950118600026646813213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154767866982933404391501901 58037950118600026646813213)
        ·
          refine ⟨21764231294475009992554955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58037950118600026646813213 21764231294475009992554955)
          ·
            refine ⟨32646346941712514988832433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21764231294475009992554955 32646346941712514988832433)
            ·
              refine ⟨24484760206284386241624325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32646346941712514988832433 24484760206284386241624325)
              ·
                refine ⟨4590892538678322420304561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24484760206284386241624325 4590892538678322420304561)
                ·
                  refine ⟨3443169404008741815228421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4590892538678322420304561 3443169404008741815228421)
                  ·
                    refine ⟨645594263251639090355329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3443169404008741815228421 645594263251639090355329)
                    ·
                      rfl

theorem cell23_3771871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 4].length) (baseStart_3771871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771871 prefixEnd_3771871 := by exact prefixLift 3771871
  have htrace : WordTrace (prefixWord ++ tailWord_3771871) baseStart_3771871 baseEnd_3771871 := by
    simpa [prefixWord, tailWord_3771871, baseEnd_3771871] using wordTrace_append hprefix tailTrace_3771871
  have hstable : (prefixWord ++ tailWord_3771871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771871).length < 2 ^ (prefixWord ++ tailWord_3771871).sum := by decide
  have hdescent : baseEnd_3771871 < baseStart_3771871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771888 : List Nat := [2, 1, 1, 1, 3, 4, 4, 1, 2, 4]
def baseStart_3771888 : Nat := 118140960795 + 3771888 * 2 ^ 59
def prefixEnd_3771888 : Nat := 4983230072969 + 3 ^ 40 * 3771888 * 2
def baseEnd_3771888 : Nat := 645597172975347901517803

theorem tailTrace_3771888 : CollatzResearch.WordTrace tailWord_3771888 prefixEnd_3771888 645597172975347901517803 := by
  unfold tailWord_3771888
  simp only [CollatzResearch.WordTrace]
  refine ⟨68786028679550719014574159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91714704906067625352765545 68786028679550719014574159)
  ·
    refine ⟨103179043019326078521861239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68786028679550719014574159 103179043019326078521861239)
    ·
      refine ⟨154768564528989117782791859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103179043019326078521861239 154768564528989117782791859)
      ·
        refine ⟨232152846793483676674187789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154768564528989117782791859 232152846793483676674187789)
        ·
          refine ⟨87057317547556378752820421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232152846793483676674187789 87057317547556378752820421)
          ·
            refine ⟨16323247040166821016153829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87057317547556378752820421 16323247040166821016153829)
            ·
              refine ⟨3060608820031278940528843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16323247040166821016153829 3060608820031278940528843)
              ·
                refine ⟨4590913230046918410793265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3060608820031278940528843 4590913230046918410793265)
                ·
                  refine ⟨3443184922535188808094949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4590913230046918410793265 3443184922535188808094949)
                  ·
                    refine ⟨645597172975347901517803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3443184922535188808094949 645597172975347901517803)
                    ·
                      rfl

theorem cell23_3771888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 2, 4].length) (baseStart_3771888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771888 prefixEnd_3771888 := by exact prefixLift 3771888
  have htrace : WordTrace (prefixWord ++ tailWord_3771888) baseStart_3771888 baseEnd_3771888 := by
    simpa [prefixWord, tailWord_3771888, baseEnd_3771888] using wordTrace_append hprefix tailTrace_3771888
  have hstable : (prefixWord ++ tailWord_3771888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771888).length < 2 ^ (prefixWord ++ tailWord_3771888).sum := by decide
  have hdescent : baseEnd_3771888 < baseStart_3771888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771908 : List Nat := [2, 3, 2, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_3771908 : Nat := 118140960795 + 3771908 * 2 ^ 59
def prefixEnd_3771908 : Nat := 4983230072969 + 3 ^ 40 * 3771908 * 2
def baseEnd_3771908 : Nat := 1936801788539133626303317

theorem tailTrace_3771908 : CollatzResearch.WordTrace tailWord_3771908 prefixEnd_3771908 1936801788539133626303317 := by
  unfold tailWord_3771908
  simp only [CollatzResearch.WordTrace]
  refine ⟨68786393409514490722438189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91715191212685987629917585 68786393409514490722438189)
  ·
    refine ⟨25794897528567934020914321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68786393409514490722438189 25794897528567934020914321)
    ·
      refine ⟨19346173146425950515685741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25794897528567934020914321 19346173146425950515685741)
      ·
        refine ⟨7254814929909731443382153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19346173146425950515685741 7254814929909731443382153)
        ·
          refine ⟨5441111197432298582536615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7254814929909731443382153 5441111197432298582536615)
          ·
            refine ⟨8161666796148447873804923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5441111197432298582536615 8161666796148447873804923)
            ·
              refine ⟨12242500194222671810707385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8161666796148447873804923 12242500194222671810707385)
              ·
                refine ⟨9181875145667003858030539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12242500194222671810707385 9181875145667003858030539)
                ·
                  refine ⟨13772812718500505787045809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9181875145667003858030539 13772812718500505787045809)
                  ·
                    refine ⟨10329609538875379340284357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13772812718500505787045809 10329609538875379340284357)
                    ·
                      refine ⟨1936801788539133626303317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10329609538875379340284357 1936801788539133626303317)
                      ·
                        rfl

theorem cell23_3771908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_3771908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771908 prefixEnd_3771908 := by exact prefixLift 3771908
  have htrace : WordTrace (prefixWord ++ tailWord_3771908) baseStart_3771908 baseEnd_3771908 := by
    simpa [prefixWord, tailWord_3771908, baseEnd_3771908] using wordTrace_append hprefix tailTrace_3771908
  have hstable : (prefixWord ++ tailWord_3771908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771908).length < 2 ^ (prefixWord ++ tailWord_3771908).sum := by decide
  have hdescent : baseEnd_3771908 < baseStart_3771908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771911 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 3]
def baseStart_3771911 : Nat := 118140960795 + 3771911 * 2 ^ 59
def prefixEnd_3771911 : Nat := 4983230072969 + 3 ^ 40 * 3771911 * 2
def baseEnd_3771911 : Nat := 1936803328981097114565803

theorem tailTrace_3771911 : CollatzResearch.WordTrace tailWord_3771911 prefixEnd_3771911 1936803328981097114565803 := by
  unfold tailWord_3771911
  simp only [CollatzResearch.WordTrace]
  refine ⟨137572896238018112957235587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91715264158678741971490391 137572896238018112957235587)
  ·
    refine ⟨206359344357027169435853381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137572896238018112957235587 206359344357027169435853381)
    ·
      refine ⟨38692377066942594269222509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206359344357027169435853381 38692377066942594269222509)
      ·
        refine ⟨14509641400103472850958441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38692377066942594269222509 14509641400103472850958441)
        ·
          refine ⟨10882231050077604638218831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14509641400103472850958441 10882231050077604638218831)
          ·
            refine ⟨16323346575116406957328247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10882231050077604638218831 16323346575116406957328247)
            ·
              refine ⟨24485019862674610435992371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16323346575116406957328247 24485019862674610435992371)
              ·
                refine ⟨36727529794011915653988557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24485019862674610435992371 36727529794011915653988557)
                ·
                  refine ⟨13772823672754468370245709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36727529794011915653988557 13772823672754468370245709)
                  ·
                    refine ⟨5164808877282925638842141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13772823672754468370245709 5164808877282925638842141)
                    ·
                      refine ⟨1936803328981097114565803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5164808877282925638842141 1936803328981097114565803)
                      ·
                        rfl

theorem cell23_3771911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_3771911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771911 prefixEnd_3771911 := by exact prefixLift 3771911
  have htrace : WordTrace (prefixWord ++ tailWord_3771911) baseStart_3771911 baseEnd_3771911 := by
    simpa [prefixWord, tailWord_3771911, baseEnd_3771911] using wordTrace_append hprefix tailTrace_3771911
  have hstable : (prefixWord ++ tailWord_3771911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771911).length < 2 ^ (prefixWord ++ tailWord_3771911).sum := by decide
  have hdescent : baseEnd_3771911 < baseStart_3771911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771915 : List Nat := [1, 1, 1, 1, 8, 1, 3, 1, 1, 2, 3]
def baseStart_3771915 : Nat := 118140960795 + 3771915 * 2 ^ 59
def prefixEnd_3771915 : Nat := 4983230072969 + 3 ^ 40 * 3771915 * 2
def baseEnd_3771915 : Nat := 1936805382903715098915785

theorem tailTrace_3771915 : CollatzResearch.WordTrace tailWord_3771915 prefixEnd_3771915 1936805382903715098915785 := by
  unfold tailWord_3771915
  simp only [CollatzResearch.WordTrace]
  refine ⟨137573042130003621640381199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91715361420002414426920799 137573042130003621640381199)
  ·
    refine ⟨206359563195005432460571799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137573042130003621640381199 206359563195005432460571799)
    ·
      refine ⟨309539344792508148690857699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206359563195005432460571799 309539344792508148690857699)
      ·
        refine ⟨464309017188762223036286549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309539344792508148690857699 464309017188762223036286549)
        ·
          refine ⟨5441121295180807301206483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 464309017188762223036286549 5441121295180807301206483)
          ·
            refine ⟨8161681942771210951809725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5441121295180807301206483 8161681942771210951809725)
            ·
              refine ⟨3060630728539204106928647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8161681942771210951809725 3060630728539204106928647)
              ·
                refine ⟨4590946092808806160392971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3060630728539204106928647 4590946092808806160392971)
                ·
                  refine ⟨6886419139213209240589457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4590946092808806160392971 6886419139213209240589457)
                  ·
                    refine ⟨5164814354409906930442093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6886419139213209240589457 5164814354409906930442093)
                    ·
                      refine ⟨1936805382903715098915785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5164814354409906930442093 1936805382903715098915785)
                      ·
                        rfl

theorem cell23_3771915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 1, 2, 3].length) (baseStart_3771915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771915 prefixEnd_3771915 := by exact prefixLift 3771915
  have htrace : WordTrace (prefixWord ++ tailWord_3771915) baseStart_3771915 baseEnd_3771915 := by
    simpa [prefixWord, tailWord_3771915, baseEnd_3771915] using wordTrace_append hprefix tailTrace_3771915
  have hstable : (prefixWord ++ tailWord_3771915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771915).length < 2 ^ (prefixWord ++ tailWord_3771915).sum := by decide
  have hdescent : baseEnd_3771915 < baseStart_3771915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771938 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 3, 3, 2]
def baseStart_3771938 : Nat := 118140960795 + 3771938 * 2 ^ 59
def prefixEnd_3771938 : Nat := 4983230072969 + 3 ^ 40 * 3771938 * 2
def baseEnd_3771938 : Nat := 1936817192958768508928179

theorem tailTrace_3771938 : CollatzResearch.WordTrace tailWord_3771938 prefixEnd_3771938 1936817192958768508928179 := by
  unfold tailWord_3771938
  simp only [CollatzResearch.WordTrace]
  refine ⟨34393470252230074142117117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91715920672613531045645645 34393470252230074142117117)
  ·
    refine ⟨12897551344586277803293919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34393470252230074142117117 12897551344586277803293919)
    ·
      refine ⟨19346327016879416704940879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12897551344586277803293919 19346327016879416704940879)
      ·
        refine ⟨29019490525319125057411319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19346327016879416704940879 29019490525319125057411319)
        ·
          refine ⟨43529235787978687586116979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29019490525319125057411319 43529235787978687586116979)
          ·
            refine ⟨65293853681968031379175469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43529235787978687586116979 65293853681968031379175469)
            ·
              refine ⟨24485195130738011767190801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65293853681968031379175469 24485195130738011767190801)
              ·
                refine ⟨18363896348053508825393101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24485195130738011767190801 18363896348053508825393101)
                ·
                  refine ⟨6886461130520065809522413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18363896348053508825393101 6886461130520065809522413)
                  ·
                    refine ⟨2582422923945024678570905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6886461130520065809522413 2582422923945024678570905)
                    ·
                      refine ⟨1936817192958768508928179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2582422923945024678570905 1936817192958768508928179)
                      ·
                        rfl

theorem cell23_3771938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_3771938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771938 prefixEnd_3771938 := by exact prefixLift 3771938
  have htrace : WordTrace (prefixWord ++ tailWord_3771938) baseStart_3771938 baseEnd_3771938 := by
    simpa [prefixWord, tailWord_3771938, baseEnd_3771938] using wordTrace_append hprefix tailTrace_3771938
  have hstable : (prefixWord ++ tailWord_3771938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771938).length < 2 ^ (prefixWord ++ tailWord_3771938).sum := by decide
  have hdescent : baseEnd_3771938 < baseStart_3771938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771968 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 4, 2, 2]
def baseStart_3771968 : Nat := 118140960795 + 3771968 * 2 ^ 59
def prefixEnd_3771968 : Nat := 4983230072969 + 3 ^ 40 * 3771968 * 2
def baseEnd_3771968 : Nat := 1936832597378403391553041

theorem tailTrace_3771968 : CollatzResearch.WordTrace tailWord_3771968 prefixEnd_3771968 1936832597378403391553041 := by
  unfold tailWord_3771968
  simp only [CollatzResearch.WordTrace]
  refine ⟨68787487599405805846030279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91716650132541074461373705 68787487599405805846030279)
  ·
    refine ⟨103181231399108708769045419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68787487599405805846030279 103181231399108708769045419)
    ·
      refine ⟨154771847098663063153568129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103181231399108708769045419 154771847098663063153568129)
      ·
        refine ⟨116078885323997297365176097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154771847098663063153568129 116078885323997297365176097)
        ·
          refine ⟨87059163992997973023882073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116078885323997297365176097 87059163992997973023882073)
          ·
            refine ⟨65294372994748479767911555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87059163992997973023882073 65294372994748479767911555)
            ·
              refine ⟨97941559492122719651867333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65294372994748479767911555 97941559492122719651867333)
              ·
                refine ⟨18364042404773009934725125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97941559492122719651867333 18364042404773009934725125)
                ·
                  refine ⟨3443257950894939362760961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18364042404773009934725125 3443257950894939362760961)
                  ·
                    refine ⟨2582443463171204522070721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3443257950894939362760961 2582443463171204522070721)
                    ·
                      refine ⟨1936832597378403391553041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2582443463171204522070721 1936832597378403391553041)
                      ·
                        rfl

theorem cell23_3771968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 4, 2, 2].length) (baseStart_3771968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771968 prefixEnd_3771968 := by exact prefixLift 3771968
  have htrace : WordTrace (prefixWord ++ tailWord_3771968) baseStart_3771968 baseEnd_3771968 := by
    simpa [prefixWord, tailWord_3771968, baseEnd_3771968] using wordTrace_append hprefix tailTrace_3771968
  have hstable : (prefixWord ++ tailWord_3771968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771968).length < 2 ^ (prefixWord ++ tailWord_3771968).sum := by decide
  have hdescent : baseEnd_3771968 < baseStart_3771968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3771991 : List Nat := [1, 1, 3, 2, 2, 4, 2, 1, 7]
def baseStart_3771991 : Nat := 118140960795 + 3771991 * 2 ^ 59
def prefixEnd_3771991 : Nat := 4983230072969 + 3 ^ 40 * 3771991 * 2
def baseEnd_3771991 : Nat := 215204934159272977951715

theorem tailTrace_3771991 : CollatzResearch.WordTrace tailWord_3771991 prefixEnd_3771991 215204934159272977951715 := by
  unfold tailWord_3771991
  simp only [CollatzResearch.WordTrace]
  refine ⟨137575814077728286620147827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91717209385152191080098551 137575814077728286620147827)
  ·
    refine ⟨206363721116592429930221741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137575814077728286620147827 206363721116592429930221741)
    ·
      refine ⟨77386395418722161223833153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206363721116592429930221741 77386395418722161223833153)
      ·
        refine ⟨58039796564041620917874865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77386395418722161223833153 58039796564041620917874865)
        ·
          refine ⟨43529847423031215688406149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58039796564041620917874865 43529847423031215688406149)
          ·
            refine ⟨8161846391818352941576153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43529847423031215688406149 8161846391818352941576153)
            ·
              refine ⟨6121384793863764706182115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8161846391818352941576153 6121384793863764706182115)
              ·
                refine ⟨9182077190795647059273173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6121384793863764706182115 9182077190795647059273173)
                ·
                  refine ⟨215204934159272977951715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9182077190795647059273173 215204934159272977951715)
                  ·
                    rfl

theorem cell23_3771991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 7].length) (baseStart_3771991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3771991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3771991 prefixEnd_3771991 := by exact prefixLift 3771991
  have htrace : WordTrace (prefixWord ++ tailWord_3771991) baseStart_3771991 baseEnd_3771991 := by
    simpa [prefixWord, tailWord_3771991, baseEnd_3771991] using wordTrace_append hprefix tailTrace_3771991
  have hstable : (prefixWord ++ tailWord_3771991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3771991).length < 2 ^ (prefixWord ++ tailWord_3771991).sum := by decide
  have hdescent : baseEnd_3771991 < baseStart_3771991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3771991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772001 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 2, 3, 3]
def baseStart_3772001 : Nat := 118140960795 + 3772001 * 2 ^ 59
def prefixEnd_3772001 : Nat := 4983230072969 + 3 ^ 40 * 3772001 * 2
def baseEnd_3772001 : Nat := 1936849542240001762440389

theorem tailTrace_3772001 : CollatzResearch.WordTrace tailWord_3772001 prefixEnd_3772001 1936849542240001762440389 := by
  unfold tailWord_3772001
  simp only [CollatzResearch.WordTrace]
  refine ⟨137576178807692058328011857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91717452538461372218674571 137576178807692058328011857)
  ·
    refine ⟨103182134105769043746008893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137576178807692058328011857 103182134105769043746008893)
    ·
      refine ⟨38693300289663391404753335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103182134105769043746008893 38693300289663391404753335)
      ·
        refine ⟨58039950434495087107130003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38693300289663391404753335 58039950434495087107130003)
        ·
          refine ⟨87059925651742630660695005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58039950434495087107130003 87059925651742630660695005)
          ·
            refine ⟨32647472119403486497760627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87059925651742630660695005 32647472119403486497760627)
            ·
              refine ⟨48971208179105229746640941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32647472119403486497760627 48971208179105229746640941)
              ·
                refine ⟨18364203067164461154990353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48971208179105229746640941 18364203067164461154990353)
                ·
                  refine ⟨13773152300373345866242765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18364203067164461154990353 13773152300373345866242765)
                  ·
                    refine ⟨5164932112640004699841037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13773152300373345866242765 5164932112640004699841037)
                    ·
                      refine ⟨1936849542240001762440389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5164932112640004699841037 1936849542240001762440389)
                      ·
                        rfl

theorem cell23_3772001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_3772001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772001 prefixEnd_3772001 := by exact prefixLift 3772001
  have htrace : WordTrace (prefixWord ++ tailWord_3772001) baseStart_3772001 baseEnd_3772001 := by
    simpa [prefixWord, tailWord_3772001, baseEnd_3772001] using wordTrace_append hprefix tailTrace_3772001
  have hstable : (prefixWord ++ tailWord_3772001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772001).length < 2 ^ (prefixWord ++ tailWord_3772001).sum := by decide
  have hdescent : baseEnd_3772001 < baseStart_3772001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772011 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 3, 7, 2]
def baseStart_3772011 : Nat := 118140960795 + 3772011 * 2 ^ 59
def prefixEnd_3772011 : Nat := 4983230072969 + 3 ^ 40 * 3772011 * 2
def baseEnd_3772011 : Nat := 1936854677046546723315343

theorem tailTrace_3772011 : CollatzResearch.WordTrace tailWord_3772011 prefixEnd_3772011 1936854677046546723315343 := by
  unfold tailWord_3772011
  simp only [CollatzResearch.WordTrace]
  refine ⟨137576543537655830035875887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91717695691770553357250591 137576543537655830035875887)
  ·
    refine ⟨206364815306483745053813831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137576543537655830035875887 206364815306483745053813831)
    ·
      refine ⟨309547222959725617580720747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206364815306483745053813831 309547222959725617580720747)
      ·
        refine ⟨464320834439588426371081121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309547222959725617580720747 464320834439588426371081121)
        ·
          refine ⟨348240625829691319778310841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464320834439588426371081121 348240625829691319778310841)
          ·
            refine ⟨261180469372268489833733131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348240625829691319778310841 261180469372268489833733131)
            ·
              refine ⟨391770704058402734750599697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261180469372268489833733131 391770704058402734750599697)
              ·
                refine ⟨293828028043802051062949773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391770704058402734750599697 293828028043802051062949773)
                ·
                  refine ⟨110185510516425769148606165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293828028043802051062949773 110185510516425769148606165)
                  ·
                    refine ⟨2582472902728728964420457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 110185510516425769148606165 2582472902728728964420457)
                    ·
                      refine ⟨1936854677046546723315343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2582472902728728964420457 1936854677046546723315343)
                      ·
                        rfl

theorem cell23_3772011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 7, 2].length) (baseStart_3772011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772011 prefixEnd_3772011 := by exact prefixLift 3772011
  have htrace : WordTrace (prefixWord ++ tailWord_3772011) baseStart_3772011 baseEnd_3772011 := by
    simpa [prefixWord, tailWord_3772011, baseEnd_3772011] using wordTrace_append hprefix tailTrace_3772011
  have hstable : (prefixWord ++ tailWord_3772011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772011).length < 2 ^ (prefixWord ++ tailWord_3772011).sum := by decide
  have hdescent : baseEnd_3772011 < baseStart_3772011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772041 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 4, 1, 4]
def baseStart_3772041 : Nat := 118140960795 + 3772041 * 2 ^ 59
def prefixEnd_3772041 : Nat := 4983230072969 + 3 ^ 40 * 3772041 * 2
def baseEnd_3772041 : Nat := 1936870081466181605940205

theorem tailTrace_3772041 : CollatzResearch.WordTrace tailWord_3772041 prefixEnd_3772041 1936870081466181605940205 := by
  unfold tailWord_3772041
  simp only [CollatzResearch.WordTrace]
  refine ⟨137577637727547145159467977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91718425151698096772978651 137577637727547145159467977)
  ·
    refine ⟨103183228295660358869600983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137577637727547145159467977 103183228295660358869600983)
    ·
      refine ⟨154774842443490538304401475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103183228295660358869600983 154774842443490538304401475)
      ·
        refine ⟨232162263665235807456602213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154774842443490538304401475 232162263665235807456602213)
        ·
          refine ⟨43530424437231713898112915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232162263665235807456602213 43530424437231713898112915)
          ·
            refine ⟨65295636655847570847169373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43530424437231713898112915 65295636655847570847169373)
            ·
              refine ⟨24485863745942839067688515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65295636655847570847169373 24485863745942839067688515)
              ·
                refine ⟨36728795618914258601532773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24485863745942839067688515 36728795618914258601532773)
                ·
                  refine ⟨6886649178546423487787395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36728795618914258601532773 6886649178546423487787395)
                  ·
                    refine ⟨10329973767819635231681093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6886649178546423487787395 10329973767819635231681093)
                    ·
                      refine ⟨1936870081466181605940205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10329973767819635231681093 1936870081466181605940205)
                      ·
                        rfl

theorem cell23_3772041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 1, 4].length) (baseStart_3772041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772041 prefixEnd_3772041 := by exact prefixLift 3772041
  have htrace : WordTrace (prefixWord ++ tailWord_3772041) baseStart_3772041 baseEnd_3772041 := by
    simpa [prefixWord, tailWord_3772041, baseEnd_3772041] using wordTrace_append hprefix tailTrace_3772041
  have hstable : (prefixWord ++ tailWord_3772041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772041).length < 2 ^ (prefixWord ++ tailWord_3772041).sum := by decide
  have hdescent : baseEnd_3772041 < baseStart_3772041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772145 : List Nat := [1, 2, 2, 2, 2, 3, 4, 1, 1, 5]
def baseStart_3772145 : Nat := 118140960795 + 3772145 * 2 ^ 59
def prefixEnd_3772145 : Nat := 4983230072969 + 3 ^ 40 * 3772145 * 2
def baseEnd_3772145 : Nat := 645641161151416399679909

theorem tailTrace_3772145 : CollatzResearch.WordTrace tailWord_3772145 prefixEnd_3772145 645641161151416399679909 := by
  unfold tailWord_3772145
  simp only [CollatzResearch.WordTrace]
  refine ⟨137581430919170370921253889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91720953946113580614169259 137581430919170370921253889)
  ·
    refine ⟨103186073189377778190940417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137581430919170370921253889 103186073189377778190940417)
    ·
      refine ⟨77389554892033333643205313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103186073189377778190940417 77389554892033333643205313)
      ·
        refine ⟨58042166169025000232403985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77389554892033333643205313 58042166169025000232403985)
        ·
          refine ⟨43531624626768750174302989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58042166169025000232403985 43531624626768750174302989)
          ·
            refine ⟨16324359235038281315363621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43531624626768750174302989 16324359235038281315363621)
            ·
              refine ⟨3060817356569677746630679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16324359235038281315363621 3060817356569677746630679)
              ·
                refine ⟨4591226034854516619946019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3060817356569677746630679 4591226034854516619946019)
                ·
                  refine ⟨6886839052281774929919029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4591226034854516619946019 6886839052281774929919029)
                  ·
                    refine ⟨645641161151416399679909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6886839052281774929919029 645641161151416399679909)
                    ·
                      rfl

theorem cell23_3772145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 1, 5].length) (baseStart_3772145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772145 prefixEnd_3772145 := by exact prefixLift 3772145
  have htrace : WordTrace (prefixWord ++ tailWord_3772145) baseStart_3772145 baseEnd_3772145 := by
    simpa [prefixWord, tailWord_3772145, baseEnd_3772145] using wordTrace_append hprefix tailTrace_3772145
  have hstable : (prefixWord ++ tailWord_3772145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772145).length < 2 ^ (prefixWord ++ tailWord_3772145).sum := by decide
  have hdescent : baseEnd_3772145 < baseStart_3772145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772168 : List Nat := [2, 1, 3, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_3772168 : Nat := 118140960795 + 3772168 * 2 ^ 59
def prefixEnd_3772168 : Nat := 4983230072969 + 3 ^ 40 * 3772168 * 2
def baseEnd_3772168 : Nat := 1936935293509302609052121

theorem tailTrace_3772168 : CollatzResearch.WordTrace tailWord_3772168 prefixEnd_3772168 1936935293509302609052121 := by
  unfold tailWord_3772168
  simp only [CollatzResearch.WordTrace]
  refine ⟨68791134899043522924670579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91721513198724697232894105 68791134899043522924670579)
  ·
    refine ⟨103186702348565284387005869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68791134899043522924670579 103186702348565284387005869)
    ·
      refine ⟨38695013380711981645127201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103186702348565284387005869 38695013380711981645127201)
      ·
        refine ⟨29021260035533986233845401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38695013380711981645127201 29021260035533986233845401)
        ·
          refine ⟨21765945026650489675384051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29021260035533986233845401 21765945026650489675384051)
          ·
            refine ⟨32648917539975734513076077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21765945026650489675384051 32648917539975734513076077)
            ·
              refine ⟨12243344077490900442403529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32648917539975734513076077 12243344077490900442403529)
              ·
                refine ⟨9182508058118175331802647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12243344077490900442403529 9182508058118175331802647)
                ·
                  refine ⟨13773762087177262997703971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9182508058118175331802647 13773762087177262997703971)
                  ·
                    refine ⟨20660643130765894496555957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13773762087177262997703971 20660643130765894496555957)
                    ·
                      refine ⟨1936935293509302609052121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20660643130765894496555957 1936935293509302609052121)
                      ·
                        rfl

theorem cell23_3772168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_3772168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772168 prefixEnd_3772168 := by exact prefixLift 3772168
  have htrace : WordTrace (prefixWord ++ tailWord_3772168) baseStart_3772168 baseEnd_3772168 := by
    simpa [prefixWord, tailWord_3772168, baseEnd_3772168] using wordTrace_append hprefix tailTrace_3772168
  have hstable : (prefixWord ++ tailWord_3772168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772168).length < 2 ^ (prefixWord ++ tailWord_3772168).sum := by decide
  have hdescent : baseEnd_3772168 < baseStart_3772168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772216 : List Nat := [2, 1, 2, 1, 3, 4, 3, 2, 1, 2, 2]
def baseStart_3772216 : Nat := 118140960795 + 3772216 * 2 ^ 59
def prefixEnd_3772216 : Nat := 4983230072969 + 3 ^ 40 * 3772216 * 2
def baseEnd_3772216 : Nat := 1936959940580718421251901

theorem tailTrace_3772216 : CollatzResearch.WordTrace tailWord_3772216 prefixEnd_3772216 1936959940580718421251901 := by
  unfold tailWord_3772216
  simp only [CollatzResearch.WordTrace]
  refine ⟨68792010250956575023544251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91722680334608766698059001 68792010250956575023544251)
  ·
    refine ⟨103188015376434862535316377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68792010250956575023544251 103188015376434862535316377)
    ·
      refine ⟨77391011532326146901487283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103188015376434862535316377 77391011532326146901487283)
      ·
        refine ⟨116086517298489220352230925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77391011532326146901487283 116086517298489220352230925)
        ·
          refine ⟨43532443986933457632086597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116086517298489220352230925 43532443986933457632086597)
          ·
            refine ⟨8162333247550023306016237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43532443986933457632086597 8162333247550023306016237)
            ·
              refine ⟨3060874967831258739756089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8162333247550023306016237 3060874967831258739756089)
              ·
                refine ⟨2295656225873444054817067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3060874967831258739756089 2295656225873444054817067)
                ·
                  refine ⟨3443484338810166082225601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2295656225873444054817067 3443484338810166082225601)
                  ·
                    refine ⟨2582613254107624561669201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3443484338810166082225601 2582613254107624561669201)
                    ·
                      refine ⟨1936959940580718421251901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2582613254107624561669201 1936959940580718421251901)
                      ·
                        rfl

theorem cell23_3772216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 1, 2, 2].length) (baseStart_3772216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772216 prefixEnd_3772216 := by exact prefixLift 3772216
  have htrace : WordTrace (prefixWord ++ tailWord_3772216) baseStart_3772216 baseEnd_3772216 := by
    simpa [prefixWord, tailWord_3772216, baseEnd_3772216] using wordTrace_append hprefix tailTrace_3772216
  have hstable : (prefixWord ++ tailWord_3772216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772216).length < 2 ^ (prefixWord ++ tailWord_3772216).sum := by decide
  have hdescent : baseEnd_3772216 < baseStart_3772216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772232 : List Nat := [2, 1, 3, 1, 1, 5, 1, 3, 2, 1, 3]
def baseStart_3772232 : Nat := 118140960795 + 3772232 * 2 ^ 59
def prefixEnd_3772232 : Nat := 4983230072969 + 3 ^ 40 * 3772232 * 2
def baseEnd_3772232 : Nat := 1936968156271190358651827

theorem tailTrace_3772232 : CollatzResearch.WordTrace tailWord_3772232 prefixEnd_3772232 1936968156271190358651827 := by
  unfold tailWord_3772232
  simp only [CollatzResearch.WordTrace]
  refine ⟨68792302034927592389835475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91723069379903456519780633 68792302034927592389835475)
  ·
    refine ⟨103188453052391388584753213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68792302034927592389835475 103188453052391388584753213)
    ·
      refine ⟨38695669894646770719282455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103188453052391388584753213 38695669894646770719282455)
      ·
        refine ⟨58043504841970156078923683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38695669894646770719282455 58043504841970156078923683)
        ·
          refine ⟨87065257262955234118385525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58043504841970156078923683 87065257262955234118385525)
          ·
            refine ⟨8162367868402053198598643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87065257262955234118385525 8162367868402053198598643)
            ·
              refine ⟨12243551802603079797897965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8162367868402053198598643 12243551802603079797897965)
              ·
                refine ⟨4591331925976154924211737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12243551802603079797897965 4591331925976154924211737)
                ·
                  refine ⟨3443498944482116193158803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4591331925976154924211737 3443498944482116193158803)
                  ·
                    refine ⟨5165248416723174289738205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3443498944482116193158803 5165248416723174289738205)
                    ·
                      refine ⟨1936968156271190358651827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5165248416723174289738205 1936968156271190358651827)
                      ·
                        rfl

theorem cell23_3772232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_3772232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772232 prefixEnd_3772232 := by exact prefixLift 3772232
  have htrace : WordTrace (prefixWord ++ tailWord_3772232) baseStart_3772232 baseEnd_3772232 := by
    simpa [prefixWord, tailWord_3772232, baseEnd_3772232] using wordTrace_append hprefix tailTrace_3772232
  have hstable : (prefixWord ++ tailWord_3772232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772232).length < 2 ^ (prefixWord ++ tailWord_3772232).sum := by decide
  have hdescent : baseEnd_3772232 < baseStart_3772232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772242 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2]
def baseStart_3772242 : Nat := 118140960795 + 3772242 * 2 ^ 59
def prefixEnd_3772242 : Nat := 4983230072969 + 3 ^ 40 * 3772242 * 2
def baseEnd_3772242 : Nat := 1936973291077735319526781

theorem tailTrace_3772242 : CollatzResearch.WordTrace tailWord_3772242 prefixEnd_3772242 1936973291077735319526781 := by
  unfold tailWord_3772242
  simp only [CollatzResearch.WordTrace]
  refine ⟨34396242199954739121883745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91723312533212637658356653 34396242199954739121883745)
  ·
    refine ⟨25797181649966054341412809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34396242199954739121883745 25797181649966054341412809)
    ·
      refine ⟨19347886237474540756059607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25797181649966054341412809 19347886237474540756059607)
      ·
        refine ⟨29021829356211811134089411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19347886237474540756059607 29021829356211811134089411)
        ·
          refine ⟨43532744034317716701134117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29021829356211811134089411 43532744034317716701134117)
          ·
            refine ⟨8162389506434571881462647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43532744034317716701134117 8162389506434571881462647)
            ·
              refine ⟨12243584259651857822193971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8162389506434571881462647 12243584259651857822193971)
              ·
                refine ⟨18365376389477786733290957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12243584259651857822193971 18365376389477786733290957)
                ·
                  refine ⟨6887016146054170024984109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18365376389477786733290957 6887016146054170024984109)
                  ·
                    refine ⟨2582631054770313759369041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6887016146054170024984109 2582631054770313759369041)
                    ·
                      refine ⟨1936973291077735319526781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2582631054770313759369041 1936973291077735319526781)
                      ·
                        rfl

theorem cell23_3772242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_3772242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772242 prefixEnd_3772242 := by exact prefixLift 3772242
  have htrace : WordTrace (prefixWord ++ tailWord_3772242) baseStart_3772242 baseEnd_3772242 := by
    simpa [prefixWord, tailWord_3772242, baseEnd_3772242] using wordTrace_append hprefix tailTrace_3772242
  have hstable : (prefixWord ++ tailWord_3772242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772242).length < 2 ^ (prefixWord ++ tailWord_3772242).sum := by decide
  have hdescent : baseEnd_3772242 < baseStart_3772242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772251 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 10]
def baseStart_3772251 : Nat := 118140960795 + 3772251 * 2 ^ 59
def prefixEnd_3772251 : Nat := 4983230072969 + 3 ^ 40 * 3772251 * 2
def baseEnd_3772251 : Nat := 1936977912403625784314239

theorem tailTrace_3772251 : CollatzResearch.WordTrace tailWord_3772251 prefixEnd_3772251 1936977912403625784314239 := by
  unfold tailWord_3772251
  simp only [CollatzResearch.WordTrace]
  refine ⟨137585297056786351024612607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91723531371190900683075071 137585297056786351024612607)
  ·
    refine ⟨206377945585179526536918911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137585297056786351024612607 206377945585179526536918911)
    ·
      refine ⟨309566918377769289805378367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206377945585179526536918911 309566918377769289805378367)
      ·
        refine ⟨464350377566653934708067551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309566918377769289805378367 464350377566653934708067551)
        ·
          refine ⟨696525566349980902062101327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464350377566653934708067551 696525566349980902062101327)
          ·
            refine ⟨1044788349524971353093151991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696525566349980902062101327 1044788349524971353093151991)
            ·
              refine ⟨1567182524287457029639727987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044788349524971353093151991 1567182524287457029639727987)
              ·
                refine ⟨2350773786431185544459591981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567182524287457029639727987 2350773786431185544459591981)
                ·
                  refine ⟨881540169911694579172346993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2350773786431185544459591981 881540169911694579172346993)
                  ·
                    refine ⟨661155127433770934379260245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 881540169911694579172346993 661155127433770934379260245)
                    ·
                      refine ⟨1936977912403625784314239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 661155127433770934379260245 1936977912403625784314239)
                      ·
                        rfl

theorem cell23_3772251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 10].length) (baseStart_3772251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772251 prefixEnd_3772251 := by exact prefixLift 3772251
  have htrace : WordTrace (prefixWord ++ tailWord_3772251) baseStart_3772251 baseEnd_3772251 := by
    simpa [prefixWord, tailWord_3772251, baseEnd_3772251] using wordTrace_append hprefix tailTrace_3772251
  have hstable : (prefixWord ++ tailWord_3772251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772251).length < 2 ^ (prefixWord ++ tailWord_3772251).sum := by decide
  have hdescent : baseEnd_3772251 < baseStart_3772251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772255 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 3, 4, 2]
def baseStart_3772255 : Nat := 118140960795 + 3772255 * 2 ^ 59
def prefixEnd_3772255 : Nat := 4983230072969 + 3 ^ 40 * 3772255 * 2
def baseEnd_3772255 : Nat := 1936979966326243768664221

theorem tailTrace_3772255 : CollatzResearch.WordTrace tailWord_3772255 prefixEnd_3772255 1936979966326243768664221 := by
  unfold tailWord_3772255
  simp only [CollatzResearch.WordTrace]
  refine ⟨137585442948771859707758219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91723628632514573138505479 137585442948771859707758219)
  ·
    refine ⟨206378164423157789561637329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137585442948771859707758219 206378164423157789561637329)
    ·
      refine ⟨154783623317368342171227997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206378164423157789561637329 154783623317368342171227997)
      ·
        refine ⟨58043858744013128314210499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154783623317368342171227997 58043858744013128314210499)
        ·
          refine ⟨87065788116019692471315749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58043858744013128314210499 87065788116019692471315749)
          ·
            refine ⟨16324835271753692338371703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87065788116019692471315749 16324835271753692338371703)
            ·
              refine ⟨24487252907630538507557555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16324835271753692338371703 24487252907630538507557555)
              ·
                refine ⟨36730879361445807761336333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24487252907630538507557555 36730879361445807761336333)
                ·
                  refine ⟨13774079760542177910501125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36730879361445807761336333 13774079760542177910501125)
                  ·
                    refine ⟨2582639955101658358218961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13774079760542177910501125 2582639955101658358218961)
                    ·
                      refine ⟨1936979966326243768664221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2582639955101658358218961 1936979966326243768664221)
                      ·
                        rfl

theorem cell23_3772255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_3772255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772255 prefixEnd_3772255 := by exact prefixLift 3772255
  have htrace : WordTrace (prefixWord ++ tailWord_3772255) baseStart_3772255 baseEnd_3772255 := by
    simpa [prefixWord, tailWord_3772255, baseEnd_3772255] using wordTrace_append hprefix tailTrace_3772255
  have hstable : (prefixWord ++ tailWord_3772255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772255).length < 2 ^ (prefixWord ++ tailWord_3772255).sum := by decide
  have hdescent : baseEnd_3772255 < baseStart_3772255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772266 : List Nat := [3, 1, 3, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_3772266 : Nat := 118140960795 + 3772266 * 2 ^ 59
def prefixEnd_3772266 : Nat := 4983230072969 + 3 ^ 40 * 3772266 * 2
def baseEnd_3772266 : Nat := 1936985614613443225626671

theorem tailTrace_3772266 : CollatzResearch.WordTrace tailWord_3772266 prefixEnd_3772266 1936985614613443225626671 := by
  unfold tailWord_3772266
  simp only [CollatzResearch.WordTrace]
  refine ⟨34396461037933002146602163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91723896101154672390939101 34396461037933002146602163)
  ·
    refine ⟨51594691556899503219903245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34396461037933002146602163 51594691556899503219903245)
    ·
      refine ⟨19348009333837313707463717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51594691556899503219903245 19348009333837313707463717)
      ·
        refine ⟨3627751750094496320149447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19348009333837313707463717 3627751750094496320149447)
        ·
          refine ⟨5441627625141744480224171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3627751750094496320149447 5441627625141744480224171)
          ·
            refine ⟨8162441437712616720336257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5441627625141744480224171 8162441437712616720336257)
            ·
              refine ⟨6121831078284462540252193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8162441437712616720336257 6121831078284462540252193)
              ·
                refine ⟨4591373308713346905189145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6121831078284462540252193 4591373308713346905189145)
                ·
                  refine ⟨3443529981535010178891859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4591373308713346905189145 3443529981535010178891859)
                  ·
                    refine ⟨5165294972302515268337789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3443529981535010178891859 5165294972302515268337789)
                    ·
                      refine ⟨1936985614613443225626671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5165294972302515268337789 1936985614613443225626671)
                      ·
                        rfl

theorem cell23_3772266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_3772266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772266 prefixEnd_3772266 := by exact prefixLift 3772266
  have htrace : WordTrace (prefixWord ++ tailWord_3772266) baseStart_3772266 baseEnd_3772266 := by
    simpa [prefixWord, tailWord_3772266, baseEnd_3772266] using wordTrace_append hprefix tailTrace_3772266
  have hstable : (prefixWord ++ tailWord_3772266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772266).length < 2 ^ (prefixWord ++ tailWord_3772266).sum := by decide
  have hdescent : baseEnd_3772266 < baseStart_3772266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772295 : List Nat := [1, 1, 4, 2, 4, 1, 1, 2, 7]
def baseStart_3772295 : Nat := 118140960795 + 3772295 * 2 ^ 59
def prefixEnd_3772295 : Nat := 4983230072969 + 3 ^ 40 * 3772295 * 2
def baseEnd_3772295 : Nat := 215222278394713734684893

theorem tailTrace_3772295 : CollatzResearch.WordTrace tailWord_3772295 prefixEnd_3772295 215222278394713734684893 := by
  unfold tailWord_3772295
  simp only [CollatzResearch.WordTrace]
  refine ⟨137586901868626946539214339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91724601245751297692809559 137586901868626946539214339)
  ·
    refine ⟨206380352802940419808821509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137586901868626946539214339 206380352802940419808821509)
    ·
      refine ⟨38696316150551328714154033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206380352802940419808821509 38696316150551328714154033)
      ·
        refine ⟨29022237112913496535615525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38696316150551328714154033 29022237112913496535615525)
        ·
          refine ⟨5441669458671280600427911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29022237112913496535615525 5441669458671280600427911)
          ·
            refine ⟨8162504188006920900641867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5441669458671280600427911 8162504188006920900641867)
            ·
              refine ⟨12243756282010381350962801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8162504188006920900641867 12243756282010381350962801)
              ·
                refine ⟨9182817211507786013222101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12243756282010381350962801 9182817211507786013222101)
                ·
                  refine ⟨215222278394713734684893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9182817211507786013222101 215222278394713734684893)
                  ·
                    rfl

theorem cell23_3772295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 7].length) (baseStart_3772295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772295 prefixEnd_3772295 := by exact prefixLift 3772295
  have htrace : WordTrace (prefixWord ++ tailWord_3772295) baseStart_3772295 baseEnd_3772295 := by
    simpa [prefixWord, tailWord_3772295, baseEnd_3772295] using wordTrace_append hprefix tailTrace_3772295
  have hstable : (prefixWord ++ tailWord_3772295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772295).length < 2 ^ (prefixWord ++ tailWord_3772295).sum := by decide
  have hdescent : baseEnd_3772295 < baseStart_3772295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772340 : List Nat := [2, 5, 2, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_3772340 : Nat := 118140960795 + 3772340 * 2 ^ 59
def prefixEnd_3772340 : Nat := 4983230072969 + 3 ^ 40 * 3772340 * 2
def baseEnd_3772340 : Nat := 1937023612181875936101331

theorem tailTrace_3772340 : CollatzResearch.WordTrace tailWord_3772340 prefixEnd_3772340 1937023612181875936101331 := by
  unfold tailWord_3772340
  simp only [CollatzResearch.WordTrace]
  refine ⟨68794271576731959612301237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91725695435642612816401649 68794271576731959612301237)
  ·
    refine ⟨6449462960318621213653241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68794271576731959612301237 6449462960318621213653241)
    ·
      refine ⟨4837097220238965910239931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6449462960318621213653241 4837097220238965910239931)
      ·
        refine ⟨7255645830358448865359897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4837097220238965910239931 7255645830358448865359897)
        ·
          refine ⟨5441734372768836649019923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7255645830358448865359897 5441734372768836649019923)
          ·
            refine ⟨8162601559153254973529885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5441734372768836649019923 8162601559153254973529885)
            ·
              refine ⟨3060975584682470615073707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8162601559153254973529885 3060975584682470615073707)
              ·
                refine ⟨4591463377023705922610561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3060975584682470615073707 4591463377023705922610561)
                ·
                  refine ⟨3443597532767779441957921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4591463377023705922610561 3443597532767779441957921)
                  ·
                    refine ⟨2582698149575834581468441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3443597532767779441957921 2582698149575834581468441)
                    ·
                      refine ⟨1937023612181875936101331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2582698149575834581468441 1937023612181875936101331)
                      ·
                        rfl

theorem cell23_3772340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_3772340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772340 prefixEnd_3772340 := by exact prefixLift 3772340
  have htrace : WordTrace (prefixWord ++ tailWord_3772340) baseStart_3772340 baseEnd_3772340 := by
    simpa [prefixWord, tailWord_3772340, baseEnd_3772340] using wordTrace_append hprefix tailTrace_3772340
  have hstable : (prefixWord ++ tailWord_3772340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772340).length < 2 ^ (prefixWord ++ tailWord_3772340).sum := by decide
  have hdescent : baseEnd_3772340 < baseStart_3772340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772368 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 8]
def baseStart_3772368 : Nat := 118140960795 + 3772368 * 2 ^ 59
def prefixEnd_3772368 : Nat := 4983230072969 + 3 ^ 40 * 3772368 * 2
def baseEnd_3772368 : Nat := 215226443293355758505689

theorem tailTrace_3772368 : CollatzResearch.WordTrace tailWord_3772368 prefixEnd_3772368 215226443293355758505689 := by
  unfold tailWord_3772368
  simp only [CollatzResearch.WordTrace]
  refine ⟨68794782198681240003310879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91726376264908320004414505 68794782198681240003310879)
  ·
    refine ⟨103192173298021860004966319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68794782198681240003310879 103192173298021860004966319)
    ·
      refine ⟨154788259947032790007449479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103192173298021860004966319 154788259947032790007449479)
      ·
        refine ⟨232182389920549185011174219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154788259947032790007449479 232182389920549185011174219)
        ·
          refine ⟨348273584880823777516761329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232182389920549185011174219 348273584880823777516761329)
          ·
            refine ⟨261205188660617833137570997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348273584880823777516761329 261205188660617833137570997)
            ·
              refine ⟨24487986436932921856647281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 261205188660617833137570997 24487986436932921856647281)
              ·
                refine ⟨18365989827699691392485461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24487986436932921856647281 18365989827699691392485461)
                ·
                  refine ⟨215226443293355758505689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18365989827699691392485461 215226443293355758505689)
                  ·
                    rfl

theorem cell23_3772368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 8].length) (baseStart_3772368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772368 prefixEnd_3772368 := by exact prefixLift 3772368
  have htrace : WordTrace (prefixWord ++ tailWord_3772368) baseStart_3772368 baseEnd_3772368 := by
    simpa [prefixWord, tailWord_3772368, baseEnd_3772368] using wordTrace_append hprefix tailTrace_3772368
  have hstable : (prefixWord ++ tailWord_3772368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772368).length < 2 ^ (prefixWord ++ tailWord_3772368).sum := by decide
  have hdescent : baseEnd_3772368 < baseStart_3772368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772412 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 5, 1, 3]
def baseStart_3772412 : Nat := 118140960795 + 3772412 * 2 ^ 59
def prefixEnd_3772412 : Nat := 4983230072969 + 3 ^ 40 * 3772412 * 2
def baseEnd_3772412 : Nat := 1937060582788999654400999

theorem tailTrace_3772412 : CollatzResearch.WordTrace tailWord_3772412 prefixEnd_3772412 1937060582788999654400999 := by
  unfold tailWord_3772412
  simp only [CollatzResearch.WordTrace]
  refine ⟨68795584604601537760611745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91727446139468717014148993 68795584604601537760611745)
  ·
    refine ⟨51596688453451153320458809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68795584604601537760611745 51596688453451153320458809)
    ·
      refine ⟨38697516340088364990344107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51596688453451153320458809 38697516340088364990344107)
      ·
        refine ⟨58046274510132547485516161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38697516340088364990344107 58046274510132547485516161)
        ·
          refine ⟨43534705882599410614137121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58046274510132547485516161 43534705882599410614137121)
          ·
            refine ⟨32651029411949557960602841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43534705882599410614137121 32651029411949557960602841)
            ·
              refine ⟨24488272058962168470452131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32651029411949557960602841 24488272058962168470452131)
              ·
                refine ⟨36732408088443252705678197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24488272058962168470452131 36732408088443252705678197)
                ·
                  refine ⟨3443663258291554941157331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36732408088443252705678197 3443663258291554941157331)
                  ·
                    refine ⟨5165494887437332411735997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3443663258291554941157331 5165494887437332411735997)
                    ·
                      refine ⟨1937060582788999654400999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5165494887437332411735997 1937060582788999654400999)
                      ·
                        rfl

theorem cell23_3772412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_3772412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772412 prefixEnd_3772412 := by exact prefixLift 3772412
  have htrace : WordTrace (prefixWord ++ tailWord_3772412) baseStart_3772412 baseEnd_3772412 := by
    simpa [prefixWord, tailWord_3772412, baseEnd_3772412] using wordTrace_append hprefix tailTrace_3772412
  have hstable : (prefixWord ++ tailWord_3772412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772412).length < 2 ^ (prefixWord ++ tailWord_3772412).sum := by decide
  have hdescent : baseEnd_3772412 < baseStart_3772412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772436 : List Nat := [2, 4, 3, 2, 1, 1, 2, 2, 6]
def baseStart_3772436 : Nat := 118140960795 + 3772436 * 2 ^ 59
def prefixEnd_3772436 : Nat := 4983230072969 + 3 ^ 40 * 3772436 * 2
def baseEnd_3772436 : Nat := 215230322924967506722321

theorem tailTrace_3772436 : CollatzResearch.WordTrace tailWord_3772436 prefixEnd_3772436 215230322924967506722321 := by
  unfold tailWord_3772436
  simp only [CollatzResearch.WordTrace]
  refine ⟨68796022280558063810048581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91728029707410751746731441 68796022280558063810048581)
  ·
    refine ⟨12899254177604636964384109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68796022280558063810048581 12899254177604636964384109)
    ·
      refine ⟨4837220316601738861644041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12899254177604636964384109 4837220316601738861644041)
      ·
        refine ⟨3627915237451304146233031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4837220316601738861644041 3627915237451304146233031)
        ·
          refine ⟨5441872856176956219349547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3627915237451304146233031 5441872856176956219349547)
          ·
            refine ⟨8162809284265434329024321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5441872856176956219349547 8162809284265434329024321)
            ·
              refine ⟨6122106963199075746768241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8162809284265434329024321 6122106963199075746768241)
              ·
                refine ⟨4591580222399306810076181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6122106963199075746768241 4591580222399306810076181)
                ·
                  refine ⟨215230322924967506722321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4591580222399306810076181 215230322924967506722321)
                  ·
                    rfl

theorem cell23_3772436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_3772436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772436 prefixEnd_3772436 := by exact prefixLift 3772436
  have htrace : WordTrace (prefixWord ++ tailWord_3772436) baseStart_3772436 baseEnd_3772436 := by
    simpa [prefixWord, tailWord_3772436, baseEnd_3772436] using wordTrace_append hprefix tailTrace_3772436
  have hstable : (prefixWord ++ tailWord_3772436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772436).length < 2 ^ (prefixWord ++ tailWord_3772436).sum := by decide
  have hdescent : baseEnd_3772436 < baseStart_3772436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772462 : List Nat := [4, 1, 3, 1, 1, 2, 1, 3, 1, 6]
def baseStart_3772462 : Nat := 118140960795 + 3772462 * 2 ^ 59
def prefixEnd_3772462 : Nat := 4983230072969 + 3 ^ 40 * 3772462 * 2
def baseEnd_3772462 : Nat := 645695418940574819591923

theorem tailTrace_3772462 : CollatzResearch.WordTrace tailWord_3772462 prefixEnd_3772462 645695418940574819591923 := by
  unfold tailWord_3772462
  simp only [CollatzResearch.WordTrace]
  refine ⟨17199124107377741757567955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91728661906014622707029093 17199124107377741757567955)
  ·
    refine ⟨25798686161066612636351933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17199124107377741757567955 25798686161066612636351933)
    ·
      refine ⟨9674507310399979738631975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25798686161066612636351933 9674507310399979738631975)
      ·
        refine ⟨14511760965599969607947963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9674507310399979738631975 14511760965599969607947963)
        ·
          refine ⟨21767641448399954411921945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14511760965599969607947963 21767641448399954411921945)
          ·
            refine ⟨16325731086299965808941459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21767641448399954411921945 16325731086299965808941459)
            ·
              refine ⟨24488596629449948713412189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16325731086299965808941459 24488596629449948713412189)
              ·
                refine ⟨9183223736043730767529571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24488596629449948713412189 9183223736043730767529571)
                ·
                  refine ⟨13774835604065596151294357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9183223736043730767529571 13774835604065596151294357)
                  ·
                    refine ⟨645695418940574819591923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13774835604065596151294357 645695418940574819591923)
                    ·
                      rfl

theorem cell23_3772462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_3772462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772462 prefixEnd_3772462 := by exact prefixLift 3772462
  have htrace : WordTrace (prefixWord ++ tailWord_3772462) baseStart_3772462 baseEnd_3772462 := by
    simpa [prefixWord, tailWord_3772462, baseEnd_3772462] using wordTrace_append hprefix tailTrace_3772462
  have hstable : (prefixWord ++ tailWord_3772462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772462).length < 2 ^ (prefixWord ++ tailWord_3772462).sum := by decide
  have hdescent : baseEnd_3772462 < baseStart_3772462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772469 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 5, 2, 2]
def baseStart_3772469 : Nat := 118140960795 + 3772469 * 2 ^ 59
def prefixEnd_3772469 : Nat := 4983230072969 + 3 ^ 40 * 3772469 * 2
def baseEnd_3772469 : Nat := 1937089851186305931388237

theorem tailTrace_3772469 : CollatzResearch.WordTrace tailWord_3772469 prefixEnd_3772469 1937089851186305931388237 := by
  unfold tailWord_3772469
  simp only [CollatzResearch.WordTrace]
  refine ⟨137593248169996574256048461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91728832113331049504032307 137593248169996574256048461)
  ·
    refine ⟨51597468063748715346018173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137593248169996574256048461 51597468063748715346018173)
    ·
      refine ⟨19349050523905768254756815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51597468063748715346018173 19349050523905768254756815)
      ·
        refine ⟨29023575785858652382135223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19349050523905768254756815 29023575785858652382135223)
        ·
          refine ⟨43535363678787978573202835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29023575785858652382135223 43535363678787978573202835)
          ·
            refine ⟨65303045518181967859804253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43535363678787978573202835 65303045518181967859804253)
            ·
              refine ⟨24488642069318237947426595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65303045518181967859804253 24488642069318237947426595)
              ·
                refine ⟨36732963103977356921139893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24488642069318237947426595 36732963103977356921139893)
                ·
                  refine ⟨3443715290997877211356865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36732963103977356921139893 3443715290997877211356865)
                  ·
                    refine ⟨2582786468248407908517649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3443715290997877211356865 2582786468248407908517649)
                    ·
                      refine ⟨1937089851186305931388237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2582786468248407908517649 1937089851186305931388237)
                      ·
                        rfl

theorem cell23_3772469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_3772469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772469 prefixEnd_3772469 := by exact prefixLift 3772469
  have htrace : WordTrace (prefixWord ++ tailWord_3772469) baseStart_3772469 baseEnd_3772469 := by
    simpa [prefixWord, tailWord_3772469, baseEnd_3772469] using wordTrace_append hprefix tailTrace_3772469
  have hstable : (prefixWord ++ tailWord_3772469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772469).length < 2 ^ (prefixWord ++ tailWord_3772469).sum := by decide
  have hdescent : baseEnd_3772469 < baseStart_3772469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772473 : List Nat := [1, 2, 1, 5, 4, 1, 1, 1, 2, 3, 2]
def baseStart_3772473 : Nat := 118140960795 + 3772473 * 2 ^ 59
def prefixEnd_3772473 : Nat := 4983230072969 + 3 ^ 40 * 3772473 * 2
def baseEnd_3772473 : Nat := 1937091905108923915738219

theorem tailTrace_3772473 : CollatzResearch.WordTrace tailWord_3772473 prefixEnd_3772473 1937091905108923915738219 := by
  unfold tailWord_3772473
  simp only [CollatzResearch.WordTrace]
  refine ⟨137593394061982082939194073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91728929374654721959462715 137593394061982082939194073)
  ·
    refine ⟨103195045546486562204395555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137593394061982082939194073 103195045546486562204395555)
    ·
      refine ⟨154792568319729843306593333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103195045546486562204395555 154792568319729843306593333)
      ·
        refine ⟨14511803279974672809993125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154792568319729843306593333 14511803279974672809993125)
        ·
          refine ⟨2720963114995251151873711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14511803279974672809993125 2720963114995251151873711)
          ·
            refine ⟨4081444672492876727810567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2720963114995251151873711 4081444672492876727810567)
            ·
              refine ⟨6122167008739315091715851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4081444672492876727810567 6122167008739315091715851)
              ·
                refine ⟨9183250513108972637573777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6122167008739315091715851 9183250513108972637573777)
                ·
                  refine ⟨6887437884831729478180333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9183250513108972637573777 6887437884831729478180333)
                  ·
                    refine ⟨2582789206811898554317625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6887437884831729478180333 2582789206811898554317625)
                    ·
                      refine ⟨1937091905108923915738219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2582789206811898554317625 1937091905108923915738219)
                      ·
                        rfl

theorem cell23_3772473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_3772473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772473 prefixEnd_3772473 := by exact prefixLift 3772473
  have htrace : WordTrace (prefixWord ++ tailWord_3772473) baseStart_3772473 baseEnd_3772473 := by
    simpa [prefixWord, tailWord_3772473, baseEnd_3772473] using wordTrace_append hprefix tailTrace_3772473
  have hstable : (prefixWord ++ tailWord_3772473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772473).length < 2 ^ (prefixWord ++ tailWord_3772473).sum := by decide
  have hdescent : baseEnd_3772473 < baseStart_3772473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772486 : List Nat := [6, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_3772486 : Nat := 118140960795 + 3772486 * 2 ^ 59
def prefixEnd_3772486 : Nat := 4983230072969 + 3 ^ 40 * 3772486 * 2
def baseEnd_3772486 : Nat := 1937098580357432364875659

theorem tailTrace_3772486 : CollatzResearch.WordTrace tailWord_3772486 prefixEnd_3772486 1937098580357432364875659 := by
  unfold tailWord_3772486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4299808381591718317481791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91729245473956657439611541 4299808381591718317481791)
  ·
    refine ⟨6449712572387577476222687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4299808381591718317481791 6449712572387577476222687)
    ·
      refine ⟨9674568858581366214334031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6449712572387577476222687 9674568858581366214334031)
      ·
        refine ⟨14511853287872049321501047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9674568858581366214334031 14511853287872049321501047)
        ·
          refine ⟨21767779931808073982251571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14511853287872049321501047 21767779931808073982251571)
          ·
            refine ⟨32651669897712110973377357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21767779931808073982251571 32651669897712110973377357)
            ·
              refine ⟨12244376211642041615016509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32651669897712110973377357 12244376211642041615016509)
              ·
                refine ⟨4591641079365765605631191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12244376211642041615016509 4591641079365765605631191)
                ·
                  refine ⟨6887461619048648408446787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4591641079365765605631191 6887461619048648408446787)
                  ·
                    refine ⟨10331192428572972612670181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6887461619048648408446787 10331192428572972612670181)
                    ·
                      refine ⟨1937098580357432364875659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10331192428572972612670181 1937098580357432364875659)
                      ·
                        rfl

theorem cell23_3772486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_3772486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772486 prefixEnd_3772486 := by exact prefixLift 3772486
  have htrace : WordTrace (prefixWord ++ tailWord_3772486) baseStart_3772486 baseEnd_3772486 := by
    simpa [prefixWord, tailWord_3772486, baseEnd_3772486] using wordTrace_append hprefix tailTrace_3772486
  have hstable : (prefixWord ++ tailWord_3772486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772486).length < 2 ^ (prefixWord ++ tailWord_3772486).sum := by decide
  have hdescent : baseEnd_3772486 < baseStart_3772486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772562 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3772562 : Nat := 118140960795 + 3772562 * 2 ^ 59
def prefixEnd_3772562 : Nat := 4983230072969 + 3 ^ 40 * 3772562 * 2
def baseEnd_3772562 : Nat := 1937137604887174067525309

theorem tailTrace_3772562 : CollatzResearch.WordTrace tailWord_3772562 prefixEnd_3772562 1937137604887174067525309 := by
  unfold tailWord_3772562
  simp only [CollatzResearch.WordTrace]
  refine ⟨34399160039664912784795985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91731093439106434092789293 34399160039664912784795985)
  ·
    refine ⟨25799370029748684588596989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34399160039664912784795985 25799370029748684588596989)
    ·
      refine ⟨9674763761155756720723871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25799370029748684588596989 9674763761155756720723871)
      ·
        refine ⟨14512145641733635081085807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9674763761155756720723871 14512145641733635081085807)
        ·
          refine ⟨21768218462600452621628711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14512145641733635081085807 21768218462600452621628711)
          ·
            refine ⟨32652327693900678932443067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21768218462600452621628711 32652327693900678932443067)
            ·
              refine ⟨48978491540851018398664601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32652327693900678932443067 48978491540851018398664601)
              ·
                refine ⟨36733868655638263798998451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48978491540851018398664601 36733868655638263798998451)
                ·
                  refine ⟨55100802983457395698497677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36733868655638263798998451 55100802983457395698497677)
                  ·
                    refine ⟨20662801118796523386936629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55100802983457395698497677 20662801118796523386936629)
                    ·
                      refine ⟨1937137604887174067525309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20662801118796523386936629 1937137604887174067525309)
                      ·
                        rfl

theorem cell23_3772562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3772562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772562 prefixEnd_3772562 := by exact prefixLift 3772562
  have htrace : WordTrace (prefixWord ++ tailWord_3772562) baseStart_3772562 baseEnd_3772562 := by
    simpa [prefixWord, tailWord_3772562, baseEnd_3772562] using wordTrace_append hprefix tailTrace_3772562
  have hstable : (prefixWord ++ tailWord_3772562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772562).length < 2 ^ (prefixWord ++ tailWord_3772562).sum := by decide
  have hdescent : baseEnd_3772562 < baseStart_3772562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772570 : List Nat := [3, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3]
def baseStart_3772570 : Nat := 118140960795 + 3772570 * 2 ^ 59
def prefixEnd_3772570 : Nat := 4983230072969 + 3 ^ 40 * 3772570 * 2
def baseEnd_3772570 : Nat := 1937141712732410036225273

theorem tailTrace_3772570 : CollatzResearch.WordTrace tailWord_3772570 prefixEnd_3772570 1937141712732410036225273 := by
  unfold tailWord_3772570
  simp only [CollatzResearch.WordTrace]
  refine ⟨34399232985657667126368791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91731287961753779003650109 34399232985657667126368791)
  ·
    refine ⟨51598849478486500689553187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34399232985657667126368791 51598849478486500689553187)
    ·
      refine ⟨77398274217729751034329781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51598849478486500689553187 77398274217729751034329781)
      ·
        refine ⟨7256088207912164159468417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77398274217729751034329781 7256088207912164159468417)
        ·
          refine ⟨5442066155934123119601313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7256088207912164159468417 5442066155934123119601313)
          ·
            refine ⟨4081549616950592339700985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5442066155934123119601313 4081549616950592339700985)
            ·
              refine ⟨3061162212712944254775739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4081549616950592339700985 3061162212712944254775739)
              ·
                refine ⟨4591743319069416382163609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061162212712944254775739 4591743319069416382163609)
                ·
                  refine ⟨3443807489302062286622707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4591743319069416382163609 3443807489302062286622707)
                  ·
                    refine ⟨5165711233953093429934061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3443807489302062286622707 5165711233953093429934061)
                    ·
                      refine ⟨1937141712732410036225273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5165711233953093429934061 1937141712732410036225273)
                      ·
                        rfl

theorem cell23_3772570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_3772570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772570 prefixEnd_3772570 := by exact prefixLift 3772570
  have htrace : WordTrace (prefixWord ++ tailWord_3772570) baseStart_3772570 baseEnd_3772570 := by
    simpa [prefixWord, tailWord_3772570, baseEnd_3772570] using wordTrace_append hprefix tailTrace_3772570
  have hstable : (prefixWord ++ tailWord_3772570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772570).length < 2 ^ (prefixWord ++ tailWord_3772570).sum := by decide
  have hdescent : baseEnd_3772570 < baseStart_3772570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772572 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_3772572 : Nat := 118140960795 + 3772572 * 2 ^ 59
def prefixEnd_3772572 : Nat := 4983230072969 + 3 ^ 40 * 3772572 * 2
def baseEnd_3772572 : Nat := 1937142739693719028400263

theorem tailTrace_3772572 : CollatzResearch.WordTrace tailWord_3772572 prefixEnd_3772572 1937142739693719028400263 := by
  unfold tailWord_3772572
  simp only [CollatzResearch.WordTrace]
  refine ⟨68798502444311711423523985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91731336592415615231365313 68798502444311711423523985)
  ·
    refine ⟨51598876833233783567642989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68798502444311711423523985 51598876833233783567642989)
    ·
      refine ⟨19349578812462668837866121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51598876833233783567642989 19349578812462668837866121)
      ·
        refine ⟨14512184109347001628399591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19349578812462668837866121 14512184109347001628399591)
        ·
          refine ⟨21768276164020502442599387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14512184109347001628399591 21768276164020502442599387)
          ·
            refine ⟨32652414246030753663899081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21768276164020502442599387 32652414246030753663899081)
            ·
              refine ⟨24489310684523065247924311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32652414246030753663899081 24489310684523065247924311)
              ·
                refine ⟨36733966026784597871886467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24489310684523065247924311 36733966026784597871886467)
                ·
                  refine ⟨55100949040176896807829701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36733966026784597871886467 55100949040176896807829701)
                  ·
                    refine ⟨10331427945033168151468069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55100949040176896807829701 10331427945033168151468069)
                    ·
                      refine ⟨1937142739693719028400263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10331427945033168151468069 1937142739693719028400263)
                      ·
                        rfl

theorem cell23_3772572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_3772572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772572 prefixEnd_3772572 := by exact prefixLift 3772572
  have htrace : WordTrace (prefixWord ++ tailWord_3772572) baseStart_3772572 baseEnd_3772572 := by
    simpa [prefixWord, tailWord_3772572, baseEnd_3772572] using wordTrace_append hprefix tailTrace_3772572
  have hstable : (prefixWord ++ tailWord_3772572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772572).length < 2 ^ (prefixWord ++ tailWord_3772572).sum := by decide
  have hdescent : baseEnd_3772572 < baseStart_3772572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772580 : List Nat := [2, 3, 1, 2, 5, 1, 1, 2, 1, 3, 2]
def baseStart_3772580 : Nat := 118140960795 + 3772580 * 2 ^ 59
def prefixEnd_3772580 : Nat := 4983230072969 + 3 ^ 40 * 3772580 * 2
def baseEnd_3772580 : Nat := 1937146847538954997100227

theorem tailTrace_3772580 : CollatzResearch.WordTrace tailWord_3772580 prefixEnd_3772580 1937146847538954997100227 := by
  unfold tailWord_3772580
  simp only [CollatzResearch.WordTrace]
  refine ⟨68798648336297220106669597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91731531115062960142226129 68798648336297220106669597)
  ·
    refine ⟨25799493126111457540001099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68798648336297220106669597 25799493126111457540001099)
    ·
      refine ⟨38699239689167186310001649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25799493126111457540001099 38699239689167186310001649)
      ·
        refine ⟨29024429766875389732501237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38699239689167186310001649 29024429766875389732501237)
        ·
          refine ⟨2721040290644567787421991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29024429766875389732501237 2721040290644567787421991)
          ·
            refine ⟨4081560435966851681132987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721040290644567787421991 4081560435966851681132987)
            ·
              refine ⟨6122340653950277521699481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4081560435966851681132987 6122340653950277521699481)
              ·
                refine ⟨4591755490462708141274611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6122340653950277521699481 4591755490462708141274611)
                ·
                  refine ⟨6887633235694062211911917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4591755490462708141274611 6887633235694062211911917)
                  ·
                    refine ⟨2582862463385273329466969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6887633235694062211911917 2582862463385273329466969)
                    ·
                      refine ⟨1937146847538954997100227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2582862463385273329466969 1937146847538954997100227)
                      ·
                        rfl

theorem cell23_3772580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_3772580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772580 prefixEnd_3772580 := by exact prefixLift 3772580
  have htrace : WordTrace (prefixWord ++ tailWord_3772580) baseStart_3772580 baseEnd_3772580 := by
    simpa [prefixWord, tailWord_3772580, baseEnd_3772580] using wordTrace_append hprefix tailTrace_3772580
  have hstable : (prefixWord ++ tailWord_3772580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772580).length < 2 ^ (prefixWord ++ tailWord_3772580).sum := by decide
  have hdescent : baseEnd_3772580 < baseStart_3772580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772669 : List Nat := [1, 4, 1, 1, 1, 1, 1, 6, 2, 2, 3]
def baseStart_3772669 : Nat := 118140960795 + 3772669 * 2 ^ 59
def prefixEnd_3772669 : Nat := 4983230072969 + 3 ^ 40 * 3772669 * 2
def baseEnd_3772669 : Nat := 1937192547317205148887317

theorem tailTrace_3772669 : CollatzResearch.WordTrace tailWord_3772669 prefixEnd_3772669 1937192547317205148887317 := by
  unfold tailWord_3772669
  simp only [CollatzResearch.WordTrace]
  refine ⟨137600542769272008413329061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91733695179514672275552707 137600542769272008413329061)
  ·
    refine ⟨25800101769238501577499199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137600542769272008413329061 25800101769238501577499199)
    ·
      refine ⟨38700152653857752366248799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25800101769238501577499199 38700152653857752366248799)
      ·
        refine ⟨58050228980786628549373199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38700152653857752366248799 58050228980786628549373199)
        ·
          refine ⟨87075343471179942824059799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58050228980786628549373199 87075343471179942824059799)
          ·
            refine ⟨130613015206769914236089699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87075343471179942824059799 130613015206769914236089699)
            ·
              refine ⟨195919522810154871354134549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130613015206769914236089699 195919522810154871354134549)
              ·
                refine ⟨9183727631726009594725057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 195919522810154871354134549 9183727631726009594725057)
                ·
                  refine ⟨6887795723794507196043793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9183727631726009594725057 6887795723794507196043793)
                  ·
                    refine ⟨5165846792845880397032845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6887795723794507196043793 5165846792845880397032845)
                    ·
                      refine ⟨1937192547317205148887317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5165846792845880397032845 1937192547317205148887317)
                      ·
                        rfl

theorem cell23_3772669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_3772669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772669 prefixEnd_3772669 := by exact prefixLift 3772669
  have htrace : WordTrace (prefixWord ++ tailWord_3772669) baseStart_3772669 baseEnd_3772669 := by
    simpa [prefixWord, tailWord_3772669, baseEnd_3772669] using wordTrace_append hprefix tailTrace_3772669
  have hstable : (prefixWord ++ tailWord_3772669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772669).length < 2 ^ (prefixWord ++ tailWord_3772669).sum := by decide
  have hdescent : baseEnd_3772669 < baseStart_3772669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772719 : List Nat := [1, 1, 2, 1, 2, 1, 6, 3, 1, 5]
def baseStart_3772719 : Nat := 118140960795 + 3772719 * 2 ^ 59
def prefixEnd_3772719 : Nat := 4983230072969 + 3 ^ 40 * 3772719 * 2
def baseEnd_3772719 : Nat := 645739407116643317754029

theorem tailTrace_3772719 : CollatzResearch.WordTrace tailWord_3772719 prefixEnd_3772719 645739407116643317754029 := by
  unfold tailWord_3772719
  simp only [CollatzResearch.WordTrace]
  refine ⟨137602366419090866952649211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91734910946060577968432807 137602366419090866952649211)
  ·
    refine ⟨206403549628636300428973817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137602366419090866952649211 206403549628636300428973817)
    ·
      refine ⟨154802662221477225321730363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206403549628636300428973817 154802662221477225321730363)
      ·
        refine ⟨232203993332215837982595545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154802662221477225321730363 232203993332215837982595545)
        ·
          refine ⟨174152994999161878486946659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232203993332215837982595545 174152994999161878486946659)
          ·
            refine ⟨261229492498742817730419989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174152994999161878486946659 261229492498742817730419989)
            ·
              refine ⟨12245132460878569581113437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 261229492498742817730419989 12245132460878569581113437)
              ·
                refine ⟨4591924672829463592917539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12245132460878569581113437 4591924672829463592917539)
                ·
                  refine ⟨6887887009244195389376309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4591924672829463592917539 6887887009244195389376309)
                  ·
                    refine ⟨645739407116643317754029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6887887009244195389376309 645739407116643317754029)
                    ·
                      rfl

theorem cell23_3772719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 5].length) (baseStart_3772719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772719 prefixEnd_3772719 := by exact prefixLift 3772719
  have htrace : WordTrace (prefixWord ++ tailWord_3772719) baseStart_3772719 baseEnd_3772719 := by
    simpa [prefixWord, tailWord_3772719, baseEnd_3772719] using wordTrace_append hprefix tailTrace_3772719
  have hstable : (prefixWord ++ tailWord_3772719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772719).length < 2 ^ (prefixWord ++ tailWord_3772719).sum := by decide
  have hdescent : baseEnd_3772719 < baseStart_3772719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772740 : List Nat := [2, 3, 4, 1, 2, 2, 2, 1, 6]
def baseStart_3772740 : Nat := 118140960795 + 3772740 * 2 ^ 59
def prefixEnd_3772740 : Nat := 4983230072969 + 3 ^ 40 * 3772740 * 2
def baseEnd_3772740 : Nat := 215247667160408263455499

theorem tailTrace_3772740 : CollatzResearch.WordTrace tailWord_3772740 prefixEnd_3772740 215247667160408263455499 := by
  unfold tailWord_3772740
  simp only [CollatzResearch.WordTrace]
  refine ⟨68801566176007393769581837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91735421568009858359442449 68801566176007393769581837)
  ·
    refine ⟨25800587316002772663593189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68801566176007393769581837 25800587316002772663593189)
    ·
      refine ⟨4837610121750519874423723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25800587316002772663593189 4837610121750519874423723)
      ·
        refine ⟨7256415182625779811635585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4837610121750519874423723 7256415182625779811635585)
        ·
          refine ⟨5442311386969334858726689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7256415182625779811635585 5442311386969334858726689)
          ·
            refine ⟨4081733540227001144045017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5442311386969334858726689 4081733540227001144045017)
            ·
              refine ⟨3061300155170250858033763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4081733540227001144045017 3061300155170250858033763)
              ·
                refine ⟨4591950232755376287050645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061300155170250858033763 4591950232755376287050645)
                ·
                  refine ⟨215247667160408263455499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4591950232755376287050645 215247667160408263455499)
                  ·
                    rfl

theorem cell23_3772740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_3772740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772740 prefixEnd_3772740 := by exact prefixLift 3772740
  have htrace : WordTrace (prefixWord ++ tailWord_3772740) baseStart_3772740 baseEnd_3772740 := by
    simpa [prefixWord, tailWord_3772740, baseEnd_3772740] using wordTrace_append hprefix tailTrace_3772740
  have hstable : (prefixWord ++ tailWord_3772740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772740).length < 2 ^ (prefixWord ++ tailWord_3772740).sum := by decide
  have hdescent : baseEnd_3772740 < baseStart_3772740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772756 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_3772756 : Nat := 118140960795 + 3772756 * 2 ^ 59
def prefixEnd_3772756 : Nat := 4983230072969 + 3 ^ 40 * 3772756 * 2
def baseEnd_3772756 : Nat := 1937237220134146308499417

theorem tailTrace_3772756 : CollatzResearch.WordTrace tailWord_3772756 prefixEnd_3772756 1937237220134146308499417 := by
  unfold tailWord_3772756
  simp only [CollatzResearch.WordTrace]
  refine ⟨68801857959978411135873061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91735810613304548181164081 68801857959978411135873061)
  ·
    refine ⟨12900348367495952087976199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68801857959978411135873061 12900348367495952087976199)
    ·
      refine ⟨19350522551243928131964299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12900348367495952087976199 19350522551243928131964299)
      ·
        refine ⟨29025783826865892197946449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19350522551243928131964299 29025783826865892197946449)
        ·
          refine ⟨21769337870149419148459837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29025783826865892197946449 21769337870149419148459837)
          ·
            refine ⟨8163501701306032180672439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21769337870149419148459837 8163501701306032180672439)
            ·
              refine ⟨12245252551959048271008659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8163501701306032180672439 12245252551959048271008659)
              ·
                refine ⟨18367878827938572406512989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12245252551959048271008659 18367878827938572406512989)
                ·
                  refine ⟨6887954560476964652442371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18367878827938572406512989 6887954560476964652442371)
                  ·
                    refine ⟨10331931840715446978663557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6887954560476964652442371 10331931840715446978663557)
                    ·
                      refine ⟨1937237220134146308499417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10331931840715446978663557 1937237220134146308499417)
                      ·
                        rfl

theorem cell23_3772756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_3772756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772756 prefixEnd_3772756 := by exact prefixLift 3772756
  have htrace : WordTrace (prefixWord ++ tailWord_3772756) baseStart_3772756 baseEnd_3772756 := by
    simpa [prefixWord, tailWord_3772756, baseEnd_3772756] using wordTrace_append hprefix tailTrace_3772756
  have hstable : (prefixWord ++ tailWord_3772756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772756).length < 2 ^ (prefixWord ++ tailWord_3772756).sum := by decide
  have hdescent : baseEnd_3772756 < baseStart_3772756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772773 : List Nat := [1, 3, 1, 3, 1, 4, 3, 1, 1, 1, 4]
def baseStart_3772773 : Nat := 118140960795 + 3772773 * 2 ^ 59
def prefixEnd_3772773 : Nat := 4983230072969 + 3 ^ 40 * 3772773 * 2
def baseEnd_3772773 : Nat := 1937245949305272741986839

theorem tailTrace_3772773 : CollatzResearch.WordTrace tailWord_3772773 prefixEnd_3772773 1937245949305272741986839 := by
  unfold tailWord_3772773
  simp only [CollatzResearch.WordTrace]
  refine ⟨137604335960895234175114973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91736223973930156116743315 137604335960895234175114973)
  ·
    refine ⟨51601625985335712815668115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137604335960895234175114973 51601625985335712815668115)
    ·
      refine ⟨77402438978003569223502173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51601625985335712815668115 77402438978003569223502173)
      ·
        refine ⟨29025914616751338458813315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77402438978003569223502173 29025914616751338458813315)
        ·
          refine ⟨43538871925127007688219973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29025914616751338458813315 43538871925127007688219973)
          ·
            refine ⟨8163538485961313941541245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43538871925127007688219973 8163538485961313941541245)
            ·
              refine ⟨3061326932235492728077967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8163538485961313941541245 3061326932235492728077967)
              ·
                refine ⟨4591990398353239092116951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061326932235492728077967 4591990398353239092116951)
                ·
                  refine ⟨6887985597529858638175427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4591990398353239092116951 6887985597529858638175427)
                  ·
                    refine ⟨10331978396294787957263141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6887985597529858638175427 10331978396294787957263141)
                    ·
                      refine ⟨1937245949305272741986839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10331978396294787957263141 1937245949305272741986839)
                      ·
                        rfl

theorem cell23_3772773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_3772773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772773 prefixEnd_3772773 := by exact prefixLift 3772773
  have htrace : WordTrace (prefixWord ++ tailWord_3772773) baseStart_3772773 baseEnd_3772773 := by
    simpa [prefixWord, tailWord_3772773, baseEnd_3772773] using wordTrace_append hprefix tailTrace_3772773
  have hstable : (prefixWord ++ tailWord_3772773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772773).length < 2 ^ (prefixWord ++ tailWord_3772773).sum := by decide
  have hdescent : baseEnd_3772773 < baseStart_3772773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772776 : List Nat := [2, 1, 4, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_3772776 : Nat := 118140960795 + 3772776 * 2 ^ 59
def prefixEnd_3772776 : Nat := 4983230072969 + 3 ^ 40 * 3772776 * 2
def baseEnd_3772776 : Nat := 1937247489747236230249325

theorem tailTrace_3772776 : CollatzResearch.WordTrace tailWord_3772776 prefixEnd_3772776 1937247489747236230249325 := by
  unfold tailWord_3772776
  simp only [CollatzResearch.WordTrace]
  refine ⟨68802222689942182843737091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91736296919922910458316121 68802222689942182843737091)
  ·
    refine ⟨103203334034913274265605637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68802222689942182843737091 103203334034913274265605637)
    ·
      refine ⟨19350625131546238924801057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103203334034913274265605637 19350625131546238924801057)
      ·
        refine ⟨14512968848659679193600793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19350625131546238924801057 14512968848659679193600793)
        ·
          refine ⟨10884726636494759395200595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14512968848659679193600793 10884726636494759395200595)
          ·
            refine ⟨16327089954742139092800893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10884726636494759395200595 16327089954742139092800893)
            ·
              refine ⟨6122658733028302159800335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16327089954742139092800893 6122658733028302159800335)
              ·
                refine ⟨9183988099542453239700503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6122658733028302159800335 9183988099542453239700503)
                ·
                  refine ⟨13775982149313679859550755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9183988099542453239700503 13775982149313679859550755)
                  ·
                    refine ⟨20663973223970519789326133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13775982149313679859550755 20663973223970519789326133)
                    ·
                      refine ⟨1937247489747236230249325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20663973223970519789326133 1937247489747236230249325)
                      ·
                        rfl

theorem cell23_3772776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_3772776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772776 prefixEnd_3772776 := by exact prefixLift 3772776
  have htrace : WordTrace (prefixWord ++ tailWord_3772776) baseStart_3772776 baseEnd_3772776 := by
    simpa [prefixWord, tailWord_3772776, baseEnd_3772776] using wordTrace_append hprefix tailTrace_3772776
  have hstable : (prefixWord ++ tailWord_3772776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772776).length < 2 ^ (prefixWord ++ tailWord_3772776).sum := by decide
  have hdescent : baseEnd_3772776 < baseStart_3772776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772840 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_3772840 : Nat := 118140960795 + 3772840 * 2 ^ 59
def prefixEnd_3772840 : Nat := 4983230072969 + 3 ^ 40 * 3772840 * 2
def baseEnd_3772840 : Nat := 1937280352509123979849031

theorem tailTrace_3772840 : CollatzResearch.WordTrace tailWord_3772840 prefixEnd_3772840 1937280352509123979849031 := by
  unfold tailWord_3772840
  simp only [CollatzResearch.WordTrace]
  refine ⟨68803389825826252308901987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91737853101101669745202649 68803389825826252308901987)
  ·
    refine ⟨103205084738739378463352981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68803389825826252308901987 103205084738739378463352981)
    ·
      refine ⟨4837738347128408365469671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103205084738739378463352981 4837738347128408365469671)
      ·
        refine ⟨7256607520692612548204507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4837738347128408365469671 7256607520692612548204507)
        ·
          refine ⟨10884911281038918822306761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7256607520692612548204507 10884911281038918822306761)
          ·
            refine ⟨8163683460779189116730071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10884911281038918822306761 8163683460779189116730071)
            ·
              refine ⟨12245525191168783675095107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8163683460779189116730071 12245525191168783675095107)
              ·
                refine ⟨18368287786753175512642661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12245525191168783675095107 18368287786753175512642661)
                ·
                  refine ⟨3444053960016220408620499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18368287786753175512642661 3444053960016220408620499)
                  ·
                    refine ⟨5166080940024330612930749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3444053960016220408620499 5166080940024330612930749)
                    ·
                      refine ⟨1937280352509123979849031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5166080940024330612930749 1937280352509123979849031)
                      ·
                        rfl

theorem cell23_3772840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_3772840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772840 prefixEnd_3772840 := by exact prefixLift 3772840
  have htrace : WordTrace (prefixWord ++ tailWord_3772840) baseStart_3772840 baseEnd_3772840 := by
    simpa [prefixWord, tailWord_3772840, baseEnd_3772840] using wordTrace_append hprefix tailTrace_3772840
  have hstable : (prefixWord ++ tailWord_3772840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772840).length < 2 ^ (prefixWord ++ tailWord_3772840).sum := by decide
  have hdescent : baseEnd_3772840 < baseStart_3772840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772970 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_3772970 : Nat := 118140960795 + 3772970 * 2 ^ 59
def prefixEnd_3772970 : Nat := 4983230072969 + 3 ^ 40 * 3772970 * 2
def baseEnd_3772970 : Nat := 1937347104994208471223433

theorem tailTrace_3772970 : CollatzResearch.WordTrace tailWord_3772970 prefixEnd_3772970 1937347104994208471223433 := by
  unfold tailWord_3772970
  simp only [CollatzResearch.WordTrace]
  refine ⟨34402880285295384205009091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91741014094121024546690909 34402880285295384205009091)
  ·
    refine ⟨51604320427943076307513637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34402880285295384205009091 51604320427943076307513637)
    ·
      refine ⟨9675810080239326807658807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51604320427943076307513637 9675810080239326807658807)
      ·
        refine ⟨14513715120358990211488211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9675810080239326807658807 14513715120358990211488211)
        ·
          refine ⟨21770572680538485317232317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14513715120358990211488211 21770572680538485317232317)
          ·
            refine ⟨8163964755201931993962119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21770572680538485317232317 8163964755201931993962119)
            ·
              refine ⟨12245947132802897990943179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8163964755201931993962119 12245947132802897990943179)
              ·
                refine ⟨18368920699204346986414769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12245947132802897990943179 18368920699204346986414769)
                ·
                  refine ⟨13776690524403260239811077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18368920699204346986414769 13776690524403260239811077)
                  ·
                    refine ⟨2583129473325611294964577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13776690524403260239811077 2583129473325611294964577)
                    ·
                      refine ⟨1937347104994208471223433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2583129473325611294964577 1937347104994208471223433)
                      ·
                        rfl

theorem cell23_3772970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_3772970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772970 prefixEnd_3772970 := by exact prefixLift 3772970
  have htrace : WordTrace (prefixWord ++ tailWord_3772970) baseStart_3772970 baseEnd_3772970 := by
    simpa [prefixWord, tailWord_3772970, baseEnd_3772970] using wordTrace_append hprefix tailTrace_3772970
  have hstable : (prefixWord ++ tailWord_3772970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772970).length < 2 ^ (prefixWord ++ tailWord_3772970).sum := by decide
  have hdescent : baseEnd_3772970 < baseStart_3772970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3772976 : List Nat := [2, 1, 1, 1, 2, 3, 4, 3, 6]
def baseStart_3772976 : Nat := 118140960795 + 3772976 * 2 ^ 59
def prefixEnd_3772976 : Nat := 4983230072969 + 3 ^ 40 * 3772976 * 2
def baseEnd_3772976 : Nat := 215261131764237271972045

theorem tailTrace_3772976 : CollatzResearch.WordTrace tailWord_3772976 prefixEnd_3772976 215261131764237271972045 := by
  unfold tailWord_3772976
  simp only [CollatzResearch.WordTrace]
  refine ⟨68805869989579899922377391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91741159986106533229836521 68805869989579899922377391)
  ·
    refine ⟨103208804984369849883566087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68805869989579899922377391 103208804984369849883566087)
    ·
      refine ⟨154813207476554774825349131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103208804984369849883566087 154813207476554774825349131)
      ·
        refine ⟨232219811214832162238023697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154813207476554774825349131 232219811214832162238023697)
        ·
          refine ⟨174164858411124121678517773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232219811214832162238023697 174164858411124121678517773)
          ·
            refine ⟨65311821904171545629444165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174164858411124121678517773 65311821904171545629444165)
            ·
              refine ⟨12245966607032164805520781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65311821904171545629444165 12245966607032164805520781)
              ·
                refine ⟨4592237477637061802070293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12245966607032164805520781 4592237477637061802070293)
                ·
                  refine ⟨215261131764237271972045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4592237477637061802070293 215261131764237271972045)
                  ·
                    rfl

theorem cell23_3772976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 6].length) (baseStart_3772976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3772976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3772976 prefixEnd_3772976 := by exact prefixLift 3772976
  have htrace : WordTrace (prefixWord ++ tailWord_3772976) baseStart_3772976 baseEnd_3772976 := by
    simpa [prefixWord, tailWord_3772976, baseEnd_3772976] using wordTrace_append hprefix tailTrace_3772976
  have hstable : (prefixWord ++ tailWord_3772976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3772976).length < 2 ^ (prefixWord ++ tailWord_3772976).sum := by decide
  have hdescent : baseEnd_3772976 < baseStart_3772976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3772976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773040 : List Nat := [2, 1, 1, 1, 7, 1, 2, 2, 1, 5]
def baseStart_3773040 : Nat := 118140960795 + 3773040 * 2 ^ 59
def prefixEnd_3773040 : Nat := 4983230072969 + 3 ^ 40 * 3773040 * 2
def baseEnd_3773040 : Nat := 645794349546674399116037

theorem tailTrace_3773040 : CollatzResearch.WordTrace tailWord_3773040 prefixEnd_3773040 645794349546674399116037 := by
  unfold tailWord_3773040
  simp only [CollatzResearch.WordTrace]
  refine ⟨68807037125463969387542287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91742716167285292516723049 68807037125463969387542287)
  ·
    refine ⟨103210555688195954081313431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68807037125463969387542287 103210555688195954081313431)
    ·
      refine ⟨154815833532293931121970147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103210555688195954081313431 154815833532293931121970147)
      ·
        refine ⟨232223750298440896682955221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154815833532293931121970147 232223750298440896682955221)
        ·
          refine ⟨5442744147619708516006763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 232223750298440896682955221 5442744147619708516006763)
          ·
            refine ⟨8164116221429562774010145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5442744147619708516006763 8164116221429562774010145)
            ·
              refine ⟨6123087166072172080507609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8164116221429562774010145 6123087166072172080507609)
              ·
                refine ⟨4592315374554129060380707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6123087166072172080507609 4592315374554129060380707)
                ·
                  refine ⟨6888473061831193590571061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4592315374554129060380707 6888473061831193590571061)
                  ·
                    refine ⟨645794349546674399116037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6888473061831193590571061 645794349546674399116037)
                    ·
                      rfl

theorem cell23_3773040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 1, 5].length) (baseStart_3773040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773040 prefixEnd_3773040 := by exact prefixLift 3773040
  have htrace : WordTrace (prefixWord ++ tailWord_3773040) baseStart_3773040 baseEnd_3773040 := by
    simpa [prefixWord, tailWord_3773040, baseEnd_3773040] using wordTrace_append hprefix tailTrace_3773040
  have hstable : (prefixWord ++ tailWord_3773040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773040).length < 2 ^ (prefixWord ++ tailWord_3773040).sum := by decide
  have hdescent : baseEnd_3773040 < baseStart_3773040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773060 : List Nat := [2, 3, 2, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_3773060 : Nat := 118140960795 + 3773060 * 2 ^ 59
def prefixEnd_3773060 : Nat := 4983230072969 + 3 ^ 40 * 3773060 * 2
def baseEnd_3773060 : Nat := 1937393318253113119098019

theorem tailTrace_3773060 : CollatzResearch.WordTrace tailWord_3773060 prefixEnd_3773060 1937393318253113119098019 := by
  unfold tailWord_3773060
  simp only [CollatzResearch.WordTrace]
  refine ⟨68807401855427741095406317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91743202473903654793875089 68807401855427741095406317)
  ·
    refine ⟨25802775695785402910777369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68807401855427741095406317 25802775695785402910777369)
    ·
      refine ⟨19352081771839052183083027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25802775695785402910777369 19352081771839052183083027)
      ·
        refine ⟨29028122657758578274624541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19352081771839052183083027 29028122657758578274624541)
        ·
          refine ⟨10885545996659466852984203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29028122657758578274624541 10885545996659466852984203)
          ·
            refine ⟨16328318994989200279476305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10885545996659466852984203 16328318994989200279476305)
            ·
              refine ⟨12246239246241900209607229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16328318994989200279476305 12246239246241900209607229)
              ·
                refine ⟨4592339717340712578602711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12246239246241900209607229 4592339717340712578602711)
                ·
                  refine ⟨6888509576011068867904067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4592339717340712578602711 6888509576011068867904067)
                  ·
                    refine ⟨10332764364016603301856101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6888509576011068867904067 10332764364016603301856101)
                    ·
                      refine ⟨1937393318253113119098019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10332764364016603301856101 1937393318253113119098019)
                      ·
                        rfl

theorem cell23_3773060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_3773060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773060 prefixEnd_3773060 := by exact prefixLift 3773060
  have htrace : WordTrace (prefixWord ++ tailWord_3773060) baseStart_3773060 baseEnd_3773060 := by
    simpa [prefixWord, tailWord_3773060, baseEnd_3773060] using wordTrace_append hprefix tailTrace_3773060
  have hstable : (prefixWord ++ tailWord_3773060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773060).length < 2 ^ (prefixWord ++ tailWord_3773060).sum := by decide
  have hdescent : baseEnd_3773060 < baseStart_3773060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773063 : List Nat := [1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 5]
def baseStart_3773063 : Nat := 118140960795 + 3773063 * 2 ^ 59
def prefixEnd_3773063 : Nat := 4983230072969 + 3 ^ 40 * 3773063 * 2
def baseEnd_3773063 : Nat := 1937394858695076607360505

theorem tailTrace_3773063 : CollatzResearch.WordTrace tailWord_3773063 prefixEnd_3773063 1937394858695076607360505 := by
  unfold tailWord_3773063
  simp only [CollatzResearch.WordTrace]
  refine ⟨137614913129844613703171843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91743275419896409135447895 137614913129844613703171843)
  ·
    refine ⟨206422369694766920554757765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137614913129844613703171843 206422369694766920554757765)
    ·
      refine ⟨38704194317768797604017081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206422369694766920554757765 38704194317768797604017081)
      ·
        refine ⟨29028145738326598203012811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38704194317768797604017081 29028145738326598203012811)
        ·
          refine ⟨43542218607489897304519217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29028145738326598203012811 43542218607489897304519217)
          ·
            refine ⟨32656663955617422978389413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43542218607489897304519217 32656663955617422978389413)
            ·
              refine ⟨6123124491678266808448015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32656663955617422978389413 6123124491678266808448015)
              ·
                refine ⟨9184686737517400212672023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6123124491678266808448015 9184686737517400212672023)
                ·
                  refine ⟨13777030106276100319008035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9184686737517400212672023 13777030106276100319008035)
                  ·
                    refine ⟨20665545159414150478512053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13777030106276100319008035 20665545159414150478512053)
                    ·
                      refine ⟨1937394858695076607360505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20665545159414150478512053 1937394858695076607360505)
                      ·
                        rfl

theorem cell23_3773063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_3773063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773063 prefixEnd_3773063 := by exact prefixLift 3773063
  have htrace : WordTrace (prefixWord ++ tailWord_3773063) baseStart_3773063 baseEnd_3773063 := by
    simpa [prefixWord, tailWord_3773063, baseEnd_3773063] using wordTrace_append hprefix tailTrace_3773063
  have hstable : (prefixWord ++ tailWord_3773063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773063).length < 2 ^ (prefixWord ++ tailWord_3773063).sum := by decide
  have hdescent : baseEnd_3773063 < baseStart_3773063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773070 : List Nat := [4, 1, 1, 3, 1, 1, 2, 4, 2, 4]
def baseStart_3773070 : Nat := 118140960795 + 3773070 * 2 ^ 59
def prefixEnd_3773070 : Nat := 4983230072969 + 3 ^ 40 * 3773070 * 2
def baseEnd_3773070 : Nat := 645799484353219359990991

theorem tailTrace_3773070 : CollatzResearch.WordTrace tailWord_3773070 prefixEnd_3773070 645799484353219359990991 := by
  unfold tailWord_3773070
  simp only [CollatzResearch.WordTrace]
  refine ⟨17201896055102406737334583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91743445627212835932451109 17201896055102406737334583)
  ·
    refine ⟨25802844082653610106001875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17201896055102406737334583 25802844082653610106001875)
    ·
      refine ⟨38704266123980415159002813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25802844082653610106001875 38704266123980415159002813)
      ·
        refine ⟨14514099796492655684626055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38704266123980415159002813 14514099796492655684626055)
        ·
          refine ⟨21771149694738983526939083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14514099796492655684626055 21771149694738983526939083)
          ·
            refine ⟨32656724542108475290408625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21771149694738983526939083 32656724542108475290408625)
            ·
              refine ⟨24492543406581356467806469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32656724542108475290408625 24492543406581356467806469)
              ·
                refine ⟨4592351888734004337713713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24492543406581356467806469 4592351888734004337713713)
                ·
                  refine ⟨3444263916550503253285285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4592351888734004337713713 3444263916550503253285285)
                  ·
                    refine ⟨645799484353219359990991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3444263916550503253285285 645799484353219359990991)
                    ·
                      rfl

theorem cell23_3773070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_3773070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773070 prefixEnd_3773070 := by exact prefixLift 3773070
  have htrace : WordTrace (prefixWord ++ tailWord_3773070) baseStart_3773070 baseEnd_3773070 := by
    simpa [prefixWord, tailWord_3773070, baseEnd_3773070] using wordTrace_append hprefix tailTrace_3773070
  have hstable : (prefixWord ++ tailWord_3773070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773070).length < 2 ^ (prefixWord ++ tailWord_3773070).sum := by decide
  have hdescent : baseEnd_3773070 < baseStart_3773070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773093 : List Nat := [1, 3, 1, 2, 1, 2, 1, 5, 1, 3, 3]
def baseStart_3773093 : Nat := 118140960795 + 3773093 * 2 ^ 59
def prefixEnd_3773093 : Nat := 4983230072969 + 3 ^ 40 * 3773093 * 2
def baseEnd_3773093 : Nat := 1937410263114711489985367

theorem tailTrace_3773093 : CollatzResearch.WordTrace tailWord_3773093 prefixEnd_3773093 1937410263114711489985367 := by
  unfold tailWord_3773093
  simp only [CollatzResearch.WordTrace]
  refine ⟨137616007319735928826763933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91744004879823952551175955 137616007319735928826763933)
  ·
    refine ⟨51606002744900973310036475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137616007319735928826763933 51606002744900973310036475)
    ·
      refine ⟨77409004117351459965054713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51606002744900973310036475 77409004117351459965054713)
      ·
        refine ⟨58056753088013594973791035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77409004117351459965054713 58056753088013594973791035)
        ·
          refine ⟨87085129632020392460686553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58056753088013594973791035 87085129632020392460686553)
          ·
            refine ⟨65313847224015294345514915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87085129632020392460686553 65313847224015294345514915)
            ·
              refine ⟨97970770836022941518272373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65313847224015294345514915 97970770836022941518272373)
              ·
                refine ⟨9184759765877150767338035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97970770836022941518272373 9184759765877150767338035)
                ·
                  refine ⟨13777139648815726151007053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9184759765877150767338035 13777139648815726151007053)
                  ·
                    refine ⟨5166427368305897306627645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13777139648815726151007053 5166427368305897306627645)
                    ·
                      refine ⟨1937410263114711489985367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5166427368305897306627645 1937410263114711489985367)
                      ·
                        rfl

theorem cell23_3773093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_3773093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773093 prefixEnd_3773093 := by exact prefixLift 3773093
  have htrace : WordTrace (prefixWord ++ tailWord_3773093) baseStart_3773093 baseEnd_3773093 := by
    simpa [prefixWord, tailWord_3773093, baseEnd_3773093] using wordTrace_append hprefix tailTrace_3773093
  have hstable : (prefixWord ++ tailWord_3773093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773093).length < 2 ^ (prefixWord ++ tailWord_3773093).sum := by decide
  have hdescent : baseEnd_3773093 < baseStart_3773093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773143 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 2, 6]
def baseStart_3773143 : Nat := 118140960795 + 3773143 * 2 ^ 59
def prefixEnd_3773143 : Nat := 4983230072969 + 3 ^ 40 * 3773143 * 2
def baseEnd_3773143 : Nat := 645811979049145431453379

theorem tailTrace_3773143 : CollatzResearch.WordTrace tailWord_3773143 prefixEnd_3773143 645811979049145431453379 := by
  unfold tailWord_3773143
  simp only [CollatzResearch.WordTrace]
  refine ⟨137617830969554787366084083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91745220646369858244056055 137617830969554787366084083)
  ·
    refine ⟨206426746454332181049126125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137617830969554787366084083 206426746454332181049126125)
    ·
      refine ⟨77410029920374567893422297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206426746454332181049126125 77410029920374567893422297)
      ·
        refine ⟨58057522440280925920066723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77410029920374567893422297 58057522440280925920066723)
        ·
          refine ⟨87086283660421388880100085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58057522440280925920066723 87086283660421388880100085)
          ·
            refine ⟨8164339093164505207509383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87086283660421388880100085 8164339093164505207509383)
            ·
              refine ⟨12246508639746757811264075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8164339093164505207509383 12246508639746757811264075)
              ·
                refine ⟨18369762959620136716896113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12246508639746757811264075 18369762959620136716896113)
                ·
                  refine ⟨13777322219715102537672085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18369762959620136716896113 13777322219715102537672085)
                  ·
                    refine ⟨645811979049145431453379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13777322219715102537672085 645811979049145431453379)
                    ·
                      rfl

theorem cell23_3773143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_3773143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773143 prefixEnd_3773143 := by exact prefixLift 3773143
  have htrace : WordTrace (prefixWord ++ tailWord_3773143) baseStart_3773143 baseEnd_3773143 := by
    simpa [prefixWord, tailWord_3773143, baseEnd_3773143] using wordTrace_append hprefix tailTrace_3773143
  have hstable : (prefixWord ++ tailWord_3773143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773143).length < 2 ^ (prefixWord ++ tailWord_3773143).sum := by decide
  have hdescent : baseEnd_3773143 < baseStart_3773143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773240 : List Nat := [2, 1, 2, 1, 3, 2, 3, 2, 2, 1, 4]
def baseStart_3773240 : Nat := 118140960795 + 3773240 * 2 ^ 59
def prefixEnd_3773240 : Nat := 4983230072969 + 3 ^ 40 * 3773240 * 2
def baseEnd_3773240 : Nat := 1937485744770922414847191

theorem tailTrace_3773240 : CollatzResearch.WordTrace tailWord_3773240 prefixEnd_3773240 1937485744770922414847191 := by
  unfold tailWord_3773240
  simp only [CollatzResearch.WordTrace]
  refine ⟨68810684425101686466182587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91747579233468915288243449 68810684425101686466182587)
  ·
    refine ⟨103216026637652529699273881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68810684425101686466182587 103216026637652529699273881)
    ·
      refine ⟨77412019978239397274455411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103216026637652529699273881 77412019978239397274455411)
      ·
        refine ⟨116118029967359095911683117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77412019978239397274455411 116118029967359095911683117)
        ·
          refine ⟨43544261237759660966881169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116118029967359095911683117 43544261237759660966881169)
          ·
            refine ⟨32658195928319745725160877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43544261237759660966881169 32658195928319745725160877)
            ·
              refine ⟨12246823473119904646935329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32658195928319745725160877 12246823473119904646935329)
              ·
                refine ⟨9185117604839928485201497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12246823473119904646935329 9185117604839928485201497)
                ·
                  refine ⟨6888838203629946363901123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9185117604839928485201497 6888838203629946363901123)
                  ·
                    refine ⟨10333257305444919545851685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6888838203629946363901123 10333257305444919545851685)
                    ·
                      refine ⟨1937485744770922414847191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10333257305444919545851685 1937485744770922414847191)
                      ·
                        rfl

theorem cell23_3773240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_3773240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773240 prefixEnd_3773240 := by exact prefixLift 3773240
  have htrace : WordTrace (prefixWord ++ tailWord_3773240) baseStart_3773240 baseEnd_3773240 := by
    simpa [prefixWord, tailWord_3773240, baseEnd_3773240] using wordTrace_append hprefix tailTrace_3773240
  have hstable : (prefixWord ++ tailWord_3773240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773240).length < 2 ^ (prefixWord ++ tailWord_3773240).sum := by decide
  have hdescent : baseEnd_3773240 < baseStart_3773240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773243 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 3]
def baseStart_3773243 : Nat := 118140960795 + 3773243 * 2 ^ 59
def prefixEnd_3773243 : Nat := 4983230072969 + 3 ^ 40 * 3773243 * 2
def baseEnd_3773243 : Nat := 1937487285212885903109677

theorem tailTrace_3773243 : CollatzResearch.WordTrace tailWord_3773243 prefixEnd_3773243 1937487285212885903109677 := by
  unfold tailWord_3773243
  simp only [CollatzResearch.WordTrace]
  refine ⟨137621478269192504444724383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91747652179461669629816255 137621478269192504444724383)
  ·
    refine ⟨206432217403788756667086575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137621478269192504444724383 206432217403788756667086575)
    ·
      refine ⟨309648326105683135000629863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206432217403788756667086575 309648326105683135000629863)
      ·
        refine ⟨464472489158524702500944795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309648326105683135000629863 464472489158524702500944795)
        ·
          refine ⟨696708733737787053751417193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464472489158524702500944795 696708733737787053751417193)
          ·
            refine ⟨522531550303340290313562895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 696708733737787053751417193 522531550303340290313562895)
            ·
              refine ⟨783797325455010435470344343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522531550303340290313562895 783797325455010435470344343)
              ·
                refine ⟨1175695988182515653205516515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 783797325455010435470344343 1175695988182515653205516515)
                ·
                  refine ⟨1763543982273773479808274773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175695988182515653205516515 1763543982273773479808274773)
                  ·
                    refine ⟨5166632760567695741625805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1763543982273773479808274773 5166632760567695741625805)
                    ·
                      refine ⟨1937487285212885903109677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5166632760567695741625805 1937487285212885903109677)
                      ·
                        rfl

theorem cell23_3773243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 3].length) (baseStart_3773243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773243 prefixEnd_3773243 := by exact prefixLift 3773243
  have htrace : WordTrace (prefixWord ++ tailWord_3773243) baseStart_3773243 baseEnd_3773243 := by
    simpa [prefixWord, tailWord_3773243, baseEnd_3773243] using wordTrace_append hprefix tailTrace_3773243
  have hstable : (prefixWord ++ tailWord_3773243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773243).length < 2 ^ (prefixWord ++ tailWord_3773243).sum := by decide
  have hdescent : baseEnd_3773243 < baseStart_3773243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773252 : List Nat := [2, 3, 4, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_3773252 : Nat := 118140960795 + 3773252 * 2 ^ 59
def prefixEnd_3773252 : Nat := 4983230072969 + 3 ^ 40 * 3773252 * 2
def baseEnd_3773252 : Nat := 1937491906538776367897137

theorem tailTrace_3773252 : CollatzResearch.WordTrace tailWord_3773252 prefixEnd_3773252 1937491906538776367897137 := by
  unfold tailWord_3773252
  simp only [CollatzResearch.WordTrace]
  refine ⟨68810903263079949490901005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91747871017439932654534673 68810903263079949490901005)
  ·
    refine ⟨25804088723654981059087877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68810903263079949490901005 25804088723654981059087877)
    ·
      refine ⟨4838266635685308948578977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25804088723654981059087877 4838266635685308948578977)
      ·
        refine ⟨3628699976763981711434233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4838266635685308948578977 3628699976763981711434233)
        ·
          refine ⟨2721524982572986283575675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3628699976763981711434233 2721524982572986283575675)
          ·
            refine ⟨4082287473859479425363513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721524982572986283575675 4082287473859479425363513)
            ·
              refine ⟨3061715605394609569022635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4082287473859479425363513 3061715605394609569022635)
              ·
                refine ⟨4592573408091914353533953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061715605394609569022635 4592573408091914353533953)
                ·
                  refine ⟨3444430056068935765150465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4592573408091914353533953 3444430056068935765150465)
                  ·
                    refine ⟨2583322542051701823862849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3444430056068935765150465 2583322542051701823862849)
                    ·
                      refine ⟨1937491906538776367897137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2583322542051701823862849 1937491906538776367897137)
                      ·
                        rfl

theorem cell23_3773252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_3773252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773252 prefixEnd_3773252 := by exact prefixLift 3773252
  have htrace : WordTrace (prefixWord ++ tailWord_3773252) baseStart_3773252 baseEnd_3773252 := by
    simpa [prefixWord, tailWord_3773252, baseEnd_3773252] using wordTrace_append hprefix tailTrace_3773252
  have hstable : (prefixWord ++ tailWord_3773252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773252).length < 2 ^ (prefixWord ++ tailWord_3773252).sum := by decide
  have hdescent : baseEnd_3773252 < baseStart_3773252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773253 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 2, 4, 4]
def baseStart_3773253 : Nat := 118140960795 + 3773253 * 2 ^ 59
def prefixEnd_3773253 : Nat := 4983230072969 + 3 ^ 40 * 3773253 * 2
def baseEnd_3773253 : Nat := 1937492420019430863984631

theorem tailTrace_3773253 : CollatzResearch.WordTrace tailWord_3773253 prefixEnd_3773253 1937492420019430863984631 := by
  unfold tailWord_3773253
  simp only [CollatzResearch.WordTrace]
  refine ⟨137621842999156276152588413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91747895332770850768392275 137621842999156276152588413)
  ·
    refine ⟨51608191124683603557220655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137621842999156276152588413 51608191124683603557220655)
    ·
      refine ⟨77412286687025405335830983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51608191124683603557220655 77412286687025405335830983)
      ·
        refine ⟨116118430030538108003746475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77412286687025405335830983 116118430030538108003746475)
        ·
          refine ⟨174177645045807162005619713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116118430030538108003746475 174177645045807162005619713)
          ·
            refine ⟨130633233784355371504214785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174177645045807162005619713 130633233784355371504214785)
            ·
              refine ⟨97974925338266528628161089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130633233784355371504214785 97974925338266528628161089)
              ·
                refine ⟨73481194003699896471120817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97974925338266528628161089 73481194003699896471120817)
                ·
                  refine ⟨55110895502774922353340613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73481194003699896471120817 55110895502774922353340613)
                  ·
                    refine ⟨10333292906770297941251365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55110895502774922353340613 10333292906770297941251365)
                    ·
                      refine ⟨1937492420019430863984631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10333292906770297941251365 1937492420019430863984631)
                      ·
                        rfl

theorem cell23_3773253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_3773253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773253 prefixEnd_3773253 := by exact prefixLift 3773253
  have htrace : WordTrace (prefixWord ++ tailWord_3773253) baseStart_3773253 baseEnd_3773253 := by
    simpa [prefixWord, tailWord_3773253, baseEnd_3773253] using wordTrace_append hprefix tailTrace_3773253
  have hstable : (prefixWord ++ tailWord_3773253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773253).length < 2 ^ (prefixWord ++ tailWord_3773253).sum := by decide
  have hdescent : baseEnd_3773253 < baseStart_3773253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773301 : List Nat := [1, 3, 4, 1, 1, 2, 4, 2, 1, 4]
def baseStart_3773301 : Nat := 118140960795 + 3773301 * 2 ^ 59
def prefixEnd_3773301 : Nat := 4983230072969 + 3 ^ 40 * 3773301 * 2
def baseEnd_3773301 : Nat := 645839022363615558728137

theorem tailTrace_3773301 : CollatzResearch.WordTrace tailWord_3773301 prefixEnd_3773301 645839022363615558728137 := by
  unfold tailWord_3773301
  simp only [CollatzResearch.WordTrace]
  refine ⟨137623593702982380350335757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91749062468654920233557171 137623593702982380350335757)
  ·
    refine ⟨51608847638618392631375909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137623593702982380350335757 51608847638618392631375909)
    ·
      refine ⟨9676658932240948618382983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51608847638618392631375909 9676658932240948618382983)
      ·
        refine ⟨14514988398361422927574475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9676658932240948618382983 14514988398361422927574475)
        ·
          refine ⟨21772482597542134391361713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14514988398361422927574475 21772482597542134391361713)
          ·
            refine ⟨16329361948156600793521285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21772482597542134391361713 16329361948156600793521285)
            ·
              refine ⟨3061755365279362648785241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16329361948156600793521285 3061755365279362648785241)
              ·
                refine ⟨2296316523959521986588931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3061755365279362648785241 2296316523959521986588931)
                ·
                  refine ⟨3444474785939282979883397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2296316523959521986588931 3444474785939282979883397)
                  ·
                    refine ⟨645839022363615558728137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3444474785939282979883397 645839022363615558728137)
                    ·
                      rfl

theorem cell23_3773301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_3773301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773301 prefixEnd_3773301 := by exact prefixLift 3773301
  have htrace : WordTrace (prefixWord ++ tailWord_3773301) baseStart_3773301 baseEnd_3773301 := by
    simpa [prefixWord, tailWord_3773301, baseEnd_3773301] using wordTrace_append hprefix tailTrace_3773301
  have hstable : (prefixWord ++ tailWord_3773301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773301).length < 2 ^ (prefixWord ++ tailWord_3773301).sum := by decide
  have hdescent : baseEnd_3773301 < baseStart_3773301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773303 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 5]
def baseStart_3773303 : Nat := 118140960795 + 3773303 * 2 ^ 59
def prefixEnd_3773303 : Nat := 4983230072969 + 3 ^ 40 * 3773303 * 2
def baseEnd_3773303 : Nat := 1937518094052155668359401

theorem tailTrace_3773303 : CollatzResearch.WordTrace tailWord_3773303 prefixEnd_3773303 1937518094052155668359401 := by
  unfold tailWord_3773303
  simp only [CollatzResearch.WordTrace]
  refine ⟨137623666648975134691908563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91749111099316756461272375 137623666648975134691908563)
  ·
    refine ⟨206435499973462702037862845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137623666648975134691908563 206435499973462702037862845)
    ·
      refine ⟨77413312490048513264198567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206435499973462702037862845 77413312490048513264198567)
      ·
        refine ⟨116119968735072769896297851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77413312490048513264198567 116119968735072769896297851)
        ·
          refine ⟨174179953102609154844446777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116119968735072769896297851 174179953102609154844446777)
          ·
            refine ⟨130634964826956866133335083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174179953102609154844446777 130634964826956866133335083)
            ·
              refine ⟨195952447240435299200002625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130634964826956866133335083 195952447240435299200002625)
              ·
                refine ⟨146964335430326474400001969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195952447240435299200002625 146964335430326474400001969)
                ·
                  refine ⟨110223251572744855800001477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146964335430326474400001969 110223251572744855800001477)
                  ·
                    refine ⟨20666859669889660462500277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110223251572744855800001477 20666859669889660462500277)
                    ·
                      refine ⟨1937518094052155668359401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20666859669889660462500277 1937518094052155668359401)
                      ·
                        rfl

theorem cell23_3773303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_3773303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773303 prefixEnd_3773303 := by exact prefixLift 3773303
  have htrace : WordTrace (prefixWord ++ tailWord_3773303) baseStart_3773303 baseEnd_3773303 := by
    simpa [prefixWord, tailWord_3773303, baseEnd_3773303] using wordTrace_append hprefix tailTrace_3773303
  have hstable : (prefixWord ++ tailWord_3773303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773303).length < 2 ^ (prefixWord ++ tailWord_3773303).sum := by decide
  have hdescent : baseEnd_3773303 < baseStart_3773303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
