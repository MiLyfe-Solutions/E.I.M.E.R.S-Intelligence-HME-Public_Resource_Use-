import V185TrunkScan23Chunk0048

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_290013 : List Nat := [1, 4, 3, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_290013 : Nat := 118140960795 + 290013 * 2 ^ 59
def prefixEnd_290013 : Nat := 4983230072969 + 3 ^ 40 * 290013 * 2
def baseEnd_290013 : Nat := 148916065052479056503761

theorem tailTrace_290013 : CollatzResearch.WordTrace tailWord_290013 prefixEnd_290013 148916065052479056503761 := by
  unfold tailWord_290013
  simp only [CollatzResearch.WordTrace]
  refine ⟨10577643098339906122202693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7051762065559937414801795 10577643098339906122202693)
  ·
    refine ⟨1983308080938732397913005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10577643098339906122202693 1983308080938732397913005)
    ·
      refine ⟨743740530352024649217377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1983308080938732397913005 743740530352024649217377)
      ·
        refine ⟨557805397764018486913033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 743740530352024649217377 557805397764018486913033)
        ·
          refine ⟨418354048323013865184775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557805397764018486913033 418354048323013865184775)
          ·
            refine ⟨627531072484520797777163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418354048323013865184775 627531072484520797777163)
            ·
              refine ⟨941296608726781196665745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627531072484520797777163 941296608726781196665745)
              ·
                refine ⟨705972456545085897499309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941296608726781196665745 705972456545085897499309)
                ·
                  refine ⟨264739671204407211562241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705972456545085897499309 264739671204407211562241)
                  ·
                    refine ⟨198554753403305408671681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 264739671204407211562241 198554753403305408671681)
                    ·
                      refine ⟨148916065052479056503761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 198554753403305408671681 148916065052479056503761)
                      ·
                        rfl

theorem cell23_290013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_290013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290013 prefixEnd_290013 := by exact prefixLift 290013
  have htrace : WordTrace (prefixWord ++ tailWord_290013) baseStart_290013 baseEnd_290013 := by
    simpa [prefixWord, tailWord_290013, baseEnd_290013] using wordTrace_append hprefix tailTrace_290013
  have hstable : (prefixWord ++ tailWord_290013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290013).length < 2 ^ (prefixWord ++ tailWord_290013).sum := by decide
  have hdescent : baseEnd_290013 < baseStart_290013 := by decide
  rcases family_descends (prefixWord ++ tailWord_290013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290029 : List Nat := [1, 5, 1, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_290029 : Nat := 118140960795 + 290029 * 2 ^ 59
def prefixEnd_290029 : Nat := 4983230072969 + 3 ^ 40 * 290029 * 2
def baseEnd_290029 : Nat := 148924280742950993903687

theorem tailTrace_290029 : CollatzResearch.WordTrace tailWord_290029 prefixEnd_290029 148924280742950993903687 := by
  unfold tailWord_290029
  simp only [CollatzResearch.WordTrace]
  refine ⟨10578226666281940854785141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7052151110854627236523427 10578226666281940854785141)
  ·
    refine ⟨991708749963931955136107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10578226666281940854785141 991708749963931955136107)
    ·
      refine ⟨1487563124945897932704161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 991708749963931955136107 1487563124945897932704161)
      ·
        refine ⟨1115672343709423449528121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1487563124945897932704161 1115672343709423449528121)
        ·
          refine ⟨836754257782067587146091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1115672343709423449528121 836754257782067587146091)
          ·
            refine ⟨1255131386673101380719137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836754257782067587146091 1255131386673101380719137)
            ·
              refine ⟨941348540004826035539353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1255131386673101380719137 941348540004826035539353)
              ·
                refine ⟨706011405003619526654515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941348540004826035539353 706011405003619526654515)
                ·
                  refine ⟨1059017107505429289981773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 706011405003619526654515 1059017107505429289981773)
                  ·
                    refine ⟨397131415314535983743165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1059017107505429289981773 397131415314535983743165)
                    ·
                      refine ⟨148924280742950993903687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 397131415314535983743165 148924280742950993903687)
                      ·
                        rfl

theorem cell23_290029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_290029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290029 prefixEnd_290029 := by exact prefixLift 290029
  have htrace : WordTrace (prefixWord ++ tailWord_290029) baseStart_290029 baseEnd_290029 := by
    simpa [prefixWord, tailWord_290029, baseEnd_290029] using wordTrace_append hprefix tailTrace_290029
  have hstable : (prefixWord ++ tailWord_290029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290029).length < 2 ^ (prefixWord ++ tailWord_290029).sum := by decide
  have hdescent : baseEnd_290029 < baseStart_290029 := by decide
  rcases family_descends (prefixWord ++ tailWord_290029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290036 : List Nat := [2, 6, 1, 2, 1, 1, 10]
def baseStart_290036 : Nat := 118140960795 + 290036 * 2 ^ 59
def prefixEnd_290036 : Nat := 4983230072969 + 3 ^ 40 * 290036 * 2
def baseEnd_290036 : Nat := 1838615742068302055755

theorem tailTrace_290036 : CollatzResearch.WordTrace tailWord_290036 prefixEnd_290036 1838615742068302055755 := by
  unfold tailWord_290036
  simp only [CollatzResearch.WordTrace]
  refine ⟨5289240988628290525144981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7052321318171054033526641 5289240988628290525144981)
  ·
    refine ⟨247933171341951118366171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5289240988628290525144981 247933171341951118366171)
    ·
      refine ⟨371899757012926677549257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247933171341951118366171 371899757012926677549257)
      ·
        refine ⟨278924817759695008161943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371899757012926677549257 278924817759695008161943)
        ·
          refine ⟨418387226639542512242915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278924817759695008161943 418387226639542512242915)
          ·
            refine ⟨627580839959313768364373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418387226639542512242915 627580839959313768364373)
            ·
              refine ⟨1838615742068302055755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 627580839959313768364373 1838615742068302055755)
              ·
                rfl

theorem cell23_290036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 10].length) (baseStart_290036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290036 prefixEnd_290036 := by exact prefixLift 290036
  have htrace : WordTrace (prefixWord ++ tailWord_290036) baseStart_290036 baseEnd_290036 := by
    simpa [prefixWord, tailWord_290036, baseEnd_290036] using wordTrace_append hprefix tailTrace_290036
  have hstable : (prefixWord ++ tailWord_290036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290036).length < 2 ^ (prefixWord ++ tailWord_290036).sum := by decide
  have hdescent : baseEnd_290036 < baseStart_290036 := by decide
  rcases family_descends (prefixWord ++ tailWord_290036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290039 : List Nat := [1, 1, 3, 1, 1, 1, 2, 7, 1, 3, 2]
def baseStart_290039 : Nat := 118140960795 + 290039 * 2 ^ 59
def prefixEnd_290039 : Nat := 4983230072969 + 3 ^ 40 * 290039 * 2
def baseEnd_290039 : Nat := 148929415549495954778641

theorem tailTrace_290039 : CollatzResearch.WordTrace tailWord_290039 prefixEnd_290039 148929415549495954778641 := by
  unfold tailWord_290039
  simp only [CollatzResearch.WordTrace]
  refine ⟨10578591396245712562649171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7052394264163808375099447 10578591396245712562649171)
  ·
    refine ⟨15867887094368568843973757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10578591396245712562649171 15867887094368568843973757)
    ·
      refine ⟨5950457660388213316490159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15867887094368568843973757 5950457660388213316490159)
      ·
        refine ⟨8925686490582319974735239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5950457660388213316490159 8925686490582319974735239)
        ·
          refine ⟨13388529735873479962102859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8925686490582319974735239 13388529735873479962102859)
          ·
            refine ⟨20082794603810219943154289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13388529735873479962102859 20082794603810219943154289)
            ·
              refine ⟨15062095952857664957365717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20082794603810219943154289 15062095952857664957365717)
              ·
                refine ⟨353017873895101522438259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15062095952857664957365717 353017873895101522438259)
                ·
                  refine ⟨529526810842652283657389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353017873895101522438259 529526810842652283657389)
                  ·
                    refine ⟨198572554065994606371521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 529526810842652283657389 198572554065994606371521)
                    ·
                      refine ⟨148929415549495954778641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 198572554065994606371521 148929415549495954778641)
                      ·
                        rfl

theorem cell23_290039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 3, 2].length) (baseStart_290039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290039 prefixEnd_290039 := by exact prefixLift 290039
  have htrace : WordTrace (prefixWord ++ tailWord_290039) baseStart_290039 baseEnd_290039 := by
    simpa [prefixWord, tailWord_290039, baseEnd_290039] using wordTrace_append hprefix tailTrace_290039
  have hstable : (prefixWord ++ tailWord_290039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290039).length < 2 ^ (prefixWord ++ tailWord_290039).sum := by decide
  have hdescent : baseEnd_290039 < baseStart_290039 := by decide
  rcases family_descends (prefixWord ++ tailWord_290039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290046 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_290046 : Nat := 118140960795 + 290046 * 2 ^ 59
def prefixEnd_290046 : Nat := 4983230072969 + 3 ^ 40 * 290046 * 2
def baseEnd_290046 : Nat := 148933009914077427391109

theorem tailTrace_290046 : CollatzResearch.WordTrace tailWord_290046 prefixEnd_290046 148933009914077427391109 := by
  unfold tailWord_290046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1322355838402544094769249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7052564471480235172102661 1322355838402544094769249)
  ·
    refine ⟨991766878801908071076937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1322355838402544094769249 991766878801908071076937)
    ·
      refine ⟨743825159101431053307703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 991766878801908071076937 743825159101431053307703)
      ·
        refine ⟨1115737738652146579961555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 743825159101431053307703 1115737738652146579961555)
        ·
          refine ⟨1673606607978219869942333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115737738652146579961555 1673606607978219869942333)
          ·
            refine ⟨627602477991832451228375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1673606607978219869942333 627602477991832451228375)
            ·
              refine ⟨941403716987748676842563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627602477991832451228375 941403716987748676842563)
              ·
                refine ⟨1412105575481623015263845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941403716987748676842563 1412105575481623015263845)
                ·
                  refine ⟨264769795402804315361971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1412105575481623015263845 264769795402804315361971)
                  ·
                    refine ⟨397154693104206473042957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 264769795402804315361971 397154693104206473042957)
                    ·
                      refine ⟨148933009914077427391109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 397154693104206473042957 148933009914077427391109)
                      ·
                        rfl

theorem cell23_290046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_290046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290046 prefixEnd_290046 := by exact prefixLift 290046
  have htrace : WordTrace (prefixWord ++ tailWord_290046) baseStart_290046 baseEnd_290046 := by
    simpa [prefixWord, tailWord_290046, baseEnd_290046] using wordTrace_append hprefix tailTrace_290046
  have hstable : (prefixWord ++ tailWord_290046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290046).length < 2 ^ (prefixWord ++ tailWord_290046).sum := by decide
  have hdescent : baseEnd_290046 < baseStart_290046 := by decide
  rcases family_descends (prefixWord ++ tailWord_290046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290062 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 2, 6]
def baseStart_290062 : Nat := 118140960795 + 290062 * 2 ^ 59
def prefixEnd_290062 : Nat := 4983230072969 + 3 ^ 40 * 290062 * 2
def baseEnd_290062 : Nat := 49647075201516454930345

theorem tailTrace_290062 : CollatzResearch.WordTrace tailWord_290062 prefixEnd_290062 49647075201516454930345 := by
  unfold tailWord_290062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1322428784395298436342055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7052953516774924993824293 1322428784395298436342055)
  ·
    refine ⟨1983643176592947654513083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1322428784395298436342055 1983643176592947654513083)
    ·
      refine ⟨2975464764889421481769625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1983643176592947654513083 2975464764889421481769625)
      ·
        refine ⟨2231598573667066111327219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2975464764889421481769625 2231598573667066111327219)
        ·
          refine ⟨3347397860500599166990829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2231598573667066111327219 3347397860500599166990829)
          ·
            refine ⟨1255274197687724687621561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3347397860500599166990829 1255274197687724687621561)
            ·
              refine ⟨941455648265793515716171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1255274197687724687621561 941455648265793515716171)
              ·
                refine ⟨1412183472398690273574257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941455648265793515716171 1412183472398690273574257)
                ·
                  refine ⟨1059137604299017705180693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1412183472398690273574257 1059137604299017705180693)
                  ·
                    refine ⟨49647075201516454930345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1059137604299017705180693 49647075201516454930345)
                    ·
                      rfl

theorem cell23_290062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_290062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290062 prefixEnd_290062 := by exact prefixLift 290062
  have htrace : WordTrace (prefixWord ++ tailWord_290062) baseStart_290062 baseEnd_290062 := by
    simpa [prefixWord, tailWord_290062, baseEnd_290062] using wordTrace_append hprefix tailTrace_290062
  have hstable : (prefixWord ++ tailWord_290062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290062).length < 2 ^ (prefixWord ++ tailWord_290062).sum := by decide
  have hdescent : baseEnd_290062 < baseStart_290062 := by decide
  rcases family_descends (prefixWord ++ tailWord_290062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290132 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_290132 : Nat := 118140960795 + 290132 * 2 ^ 59
def prefixEnd_290132 : Nat := 4983230072969 + 3 ^ 40 * 290132 * 2
def baseEnd_290132 : Nat := 148977169250364090915713

theorem tailTrace_290132 : CollatzResearch.WordTrace tailWord_290132 prefixEnd_290132 148977169250364090915713 := by
  unfold tailWord_290132
  simp only [CollatzResearch.WordTrace]
  refine ⟨5290991692454394722892325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7054655589939192963856433 5290991692454394722892325)
  ·
    refine ⟨992060942335199010542311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5290991692454394722892325 992060942335199010542311)
    ·
      refine ⟨1488091413502798515813467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 992060942335199010542311 1488091413502798515813467)
      ·
        refine ⟨2232137120254197773720201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1488091413502798515813467 2232137120254197773720201)
        ·
          refine ⟨1674102840190648330290151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2232137120254197773720201 1674102840190648330290151)
          ·
            refine ⟨2511154260285972495435227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1674102840190648330290151 2511154260285972495435227)
            ·
              refine ⟨3766731390428958743152841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2511154260285972495435227 3766731390428958743152841)
              ·
                refine ⟨2825048542821719057364631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3766731390428958743152841 2825048542821719057364631)
                ·
                  refine ⟨4237572814232578586046947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2825048542821719057364631 4237572814232578586046947)
                  ·
                    refine ⟨6356359221348867879070421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4237572814232578586046947 6356359221348867879070421)
                    ·
                      refine ⟨148977169250364090915713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6356359221348867879070421 148977169250364090915713)
                      ·
                        rfl

theorem cell23_290132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_290132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290132 prefixEnd_290132 := by exact prefixLift 290132
  have htrace : WordTrace (prefixWord ++ tailWord_290132) baseStart_290132 baseEnd_290132 := by
    simpa [prefixWord, tailWord_290132, baseEnd_290132] using wordTrace_append hprefix tailTrace_290132
  have hstable : (prefixWord ++ tailWord_290132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290132).length < 2 ^ (prefixWord ++ tailWord_290132).sum := by decide
  have hdescent : baseEnd_290132 < baseStart_290132 := by decide
  rcases family_descends (prefixWord ++ tailWord_290132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290159 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 2, 4, 2]
def baseStart_290159 : Nat := 118140960795 + 290159 * 2 ^ 59
def prefixEnd_290159 : Nat := 4983230072969 + 3 ^ 40 * 290159 * 2
def baseEnd_290159 : Nat := 148991033228035485278089

theorem tailTrace_290159 : CollatzResearch.WordTrace tailWord_290159 prefixEnd_290159 148991033228035485278089 := by
  unfold tailWord_290159
  simp only [CollatzResearch.WordTrace]
  refine ⟨10582968155810973057017531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7055312103873982038011687 10582968155810973057017531)
  ·
    refine ⟨15874452233716459585526297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10582968155810973057017531 15874452233716459585526297)
    ·
      refine ⟨11905839175287344689144723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15874452233716459585526297 11905839175287344689144723)
      ·
        refine ⟨17858758762931017033717085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11905839175287344689144723 17858758762931017033717085)
        ·
          refine ⟨6697034536099131387643907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17858758762931017033717085 6697034536099131387643907)
          ·
            refine ⟨10045551804148697081465861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6697034536099131387643907 10045551804148697081465861)
            ·
              refine ⟨1883540963277880702774849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10045551804148697081465861 1883540963277880702774849)
              ·
                refine ⟨1412655722458410527081137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1883540963277880702774849 1412655722458410527081137)
                ·
                  refine ⟨1059491791843807895310853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1412655722458410527081137 1059491791843807895310853)
                  ·
                    refine ⟨198654710970713980370785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1059491791843807895310853 198654710970713980370785)
                    ·
                      refine ⟨148991033228035485278089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 198654710970713980370785 148991033228035485278089)
                      ·
                        rfl

theorem cell23_290159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 4, 2].length) (baseStart_290159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290159 prefixEnd_290159 := by exact prefixLift 290159
  have htrace : WordTrace (prefixWord ++ tailWord_290159) baseStart_290159 baseEnd_290159 := by
    simpa [prefixWord, tailWord_290159, baseEnd_290159] using wordTrace_append hprefix tailTrace_290159
  have hstable : (prefixWord ++ tailWord_290159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290159).length < 2 ^ (prefixWord ++ tailWord_290159).sum := by decide
  have hdescent : baseEnd_290159 < baseStart_290159 := by decide
  rcases family_descends (prefixWord ++ tailWord_290159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290162 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_290162 : Nat := 118140960795 + 290162 * 2 ^ 59
def prefixEnd_290162 : Nat := 4983230072969 + 3 ^ 40 * 290162 * 2
def baseEnd_290162 : Nat := 148992573669998973540575

theorem tailTrace_290162 : CollatzResearch.WordTrace tailWord_290162 prefixEnd_290162 148992573669998973540575 := by
  unfold tailWord_290162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2645769393700026142344185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7055385049866736379584493 2645769393700026142344185)
  ·
    refine ⟨1984327045275019606758139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2645769393700026142344185 1984327045275019606758139)
    ·
      refine ⟨2976490567912529410137209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1984327045275019606758139 2976490567912529410137209)
      ·
        refine ⟨2232367925934397057602907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2976490567912529410137209 2232367925934397057602907)
        ·
          refine ⟨3348551888901595586404361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2232367925934397057602907 3348551888901595586404361)
          ·
            refine ⟨2511413916676196689803271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3348551888901595586404361 2511413916676196689803271)
            ·
              refine ⟨3767120875014295034704907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2511413916676196689803271 3767120875014295034704907)
              ·
                refine ⟨5650681312521442552057361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3767120875014295034704907 5650681312521442552057361)
                ·
                  refine ⟨4238010984391081914043021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5650681312521442552057361 4238010984391081914043021)
                  ·
                    refine ⟨1589254119146655717766133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4238010984391081914043021 1589254119146655717766133)
                    ·
                      refine ⟨148992573669998973540575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1589254119146655717766133 148992573669998973540575)
                      ·
                        rfl

theorem cell23_290162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_290162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290162 prefixEnd_290162 := by exact prefixLift 290162
  have htrace : WordTrace (prefixWord ++ tailWord_290162) baseStart_290162 baseEnd_290162 := by
    simpa [prefixWord, tailWord_290162, baseEnd_290162] using wordTrace_append hprefix tailTrace_290162
  have hstable : (prefixWord ++ tailWord_290162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290162).length < 2 ^ (prefixWord ++ tailWord_290162).sum := by decide
  have hdescent : baseEnd_290162 < baseStart_290162 := by decide
  rcases family_descends (prefixWord ++ tailWord_290162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290196 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_290196 : Nat := 118140960795 + 290196 * 2 ^ 59
def prefixEnd_290196 : Nat := 4983230072969 + 3 ^ 40 * 290196 * 2
def baseEnd_290196 : Nat := 149010032012251840515419

theorem tailTrace_290196 : CollatzResearch.WordTrace tailWord_290196 prefixEnd_290196 149010032012251840515419 := by
  unfold tailWord_290196
  simp only [CollatzResearch.WordTrace]
  refine ⟨5292158828338464188057221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7056211771117952250742961 5292158828338464188057221)
  ·
    refine ⟨992279780313462035260729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5292158828338464188057221 992279780313462035260729)
    ·
      refine ⟨744209835235096526445547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 992279780313462035260729 744209835235096526445547)
      ·
        refine ⟨1116314752852644789668321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 744209835235096526445547 1116314752852644789668321)
        ·
          refine ⟨837236064639483592251241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1116314752852644789668321 837236064639483592251241)
          ·
            refine ⟨627927048479612694188431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 837236064639483592251241 627927048479612694188431)
            ·
              refine ⟨941890572719419041282647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627927048479612694188431 941890572719419041282647)
              ·
                refine ⟨1412835859079128561923971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941890572719419041282647 1412835859079128561923971)
                ·
                  refine ⟨2119253788618692842885957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1412835859079128561923971 2119253788618692842885957)
                  ·
                    refine ⟨397360085366004908041117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2119253788618692842885957 397360085366004908041117)
                    ·
                      refine ⟨149010032012251840515419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 397360085366004908041117 149010032012251840515419)
                      ·
                        rfl

theorem cell23_290196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_290196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290196 prefixEnd_290196 := by exact prefixLift 290196
  have htrace : WordTrace (prefixWord ++ tailWord_290196) baseStart_290196 baseEnd_290196 := by
    simpa [prefixWord, tailWord_290196, baseEnd_290196] using wordTrace_append hprefix tailTrace_290196
  have hstable : (prefixWord ++ tailWord_290196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290196).length < 2 ^ (prefixWord ++ tailWord_290196).sum := by decide
  have hdescent : baseEnd_290196 < baseStart_290196 := by decide
  rcases family_descends (prefixWord ++ tailWord_290196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290216 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 8]
def baseStart_290216 : Nat := 118140960795 + 290216 * 2 ^ 59
def prefixEnd_290216 : Nat := 4983230072969 + 3 ^ 40 * 290216 * 2
def baseEnd_290216 : Nat := 16557811291704640251703

theorem tailTrace_290216 : CollatzResearch.WordTrace tailWord_290216 prefixEnd_290216 16557811291704640251703 := by
  unfold tailWord_290216
  simp only [CollatzResearch.WordTrace]
  refine ⟨5292523558302235895921251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7056698077736314527895001 5292523558302235895921251)
  ·
    refine ⟨7938785337453353843881877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5292523558302235895921251 7938785337453353843881877)
    ·
      refine ⟨372130562693125961431963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7938785337453353843881877 372130562693125961431963)
      ·
        refine ⟨558195844039688942147945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372130562693125961431963 558195844039688942147945)
        ·
          refine ⟨418646883029766706610959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 558195844039688942147945 418646883029766706610959)
          ·
            refine ⟨627970324544650059916439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418646883029766706610959 627970324544650059916439)
            ·
              refine ⟨941955486816975089874659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627970324544650059916439 941955486816975089874659)
              ·
                refine ⟨1412933230225462634811989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941955486816975089874659 1412933230225462634811989)
                ·
                  refine ⟨16557811291704640251703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1412933230225462634811989 16557811291704640251703)
                  ·
                    rfl

theorem cell23_290216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 8].length) (baseStart_290216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290216 prefixEnd_290216 := by exact prefixLift 290216
  have htrace : WordTrace (prefixWord ++ tailWord_290216) baseStart_290216 baseEnd_290216 := by
    simpa [prefixWord, tailWord_290216, baseEnd_290216] using wordTrace_append hprefix tailTrace_290216
  have hstable : (prefixWord ++ tailWord_290216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290216).length < 2 ^ (prefixWord ++ tailWord_290216).sum := by decide
  have hdescent : baseEnd_290216 < baseStart_290216 := by decide
  rcases family_descends (prefixWord ++ tailWord_290216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290249 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 1, 8, 2]
def baseStart_290249 : Nat := 118140960795 + 290249 * 2 ^ 59
def prefixEnd_290249 : Nat := 4983230072969 + 3 ^ 40 * 290249 * 2
def baseEnd_290249 : Nat := 149037246486940133152675

theorem tailTrace_290249 : CollatzResearch.WordTrace tailWord_290249 prefixEnd_290249 149037246486940133152675 := by
  unfold tailWord_290249
  simp only [CollatzResearch.WordTrace]
  refine ⟨10586250725484918427793801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7057500483656612285195867 10586250725484918427793801)
  ·
    refine ⟨7939688044113688820845351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10586250725484918427793801 7939688044113688820845351)
    ·
      refine ⟨11909532066170533231268027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7939688044113688820845351 11909532066170533231268027)
      ·
        refine ⟨17864298099255799846902041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11909532066170533231268027 17864298099255799846902041)
        ·
          refine ⟨13398223574441849885176531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17864298099255799846902041 13398223574441849885176531)
          ·
            refine ⟨20097335361662774827764797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13398223574441849885176531 20097335361662774827764797)
            ·
              refine ⟨7536500760623540560411799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20097335361662774827764797 7536500760623540560411799)
              ·
                refine ⟨11304751140935310840617699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7536500760623540560411799 11304751140935310840617699)
                ·
                  refine ⟨16957126711402966260926549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11304751140935310840617699 16957126711402966260926549)
                  ·
                    refine ⟨198716328649253510870233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16957126711402966260926549 198716328649253510870233)
                    ·
                      refine ⟨149037246486940133152675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 198716328649253510870233 149037246486940133152675)
                      ·
                        rfl

theorem cell23_290249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 8, 2].length) (baseStart_290249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290249 prefixEnd_290249 := by exact prefixLift 290249
  have htrace : WordTrace (prefixWord ++ tailWord_290249) baseStart_290249 baseEnd_290249 := by
    simpa [prefixWord, tailWord_290249, baseEnd_290249] using wordTrace_append hprefix tailTrace_290249
  have hstable : (prefixWord ++ tailWord_290249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290249).length < 2 ^ (prefixWord ++ tailWord_290249).sum := by decide
  have hdescent : baseEnd_290249 < baseStart_290249 := by decide
  rcases family_descends (prefixWord ++ tailWord_290249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290266 : List Nat := [3, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4]
def baseStart_290266 : Nat := 118140960795 + 290266 * 2 ^ 59
def prefixEnd_290266 : Nat := 4983230072969 + 3 ^ 40 * 290266 * 2
def baseEnd_290266 : Nat := 149045975658066566640097

theorem tailTrace_290266 : CollatzResearch.WordTrace tailWord_290266 prefixEnd_290266 149045975658066566640097 := by
  unfold tailWord_290266
  simp only [CollatzResearch.WordTrace]
  refine ⟨2646717691605832582790663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7057913844282220220775101 2646717691605832582790663)
  ·
    refine ⟨3970076537408748874185995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2646717691605832582790663 3970076537408748874185995)
    ·
      refine ⟨5955114806113123311278993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3970076537408748874185995 5955114806113123311278993)
      ·
        refine ⟨4466336104584842483459245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5955114806113123311278993 4466336104584842483459245)
        ·
          refine ⟨1674876039219315931297217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4466336104584842483459245 1674876039219315931297217)
          ·
            refine ⟨1256157029414486948472913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1674876039219315931297217 1256157029414486948472913)
            ·
              refine ⟨942117772060865211354685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1256157029414486948472913 942117772060865211354685)
              ·
                refine ⟨353294164522824454258007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 942117772060865211354685 353294164522824454258007)
                ·
                  refine ⟨529941246784236681387011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353294164522824454258007 529941246784236681387011)
                  ·
                    refine ⟨794911870176355022080517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 529941246784236681387011 794911870176355022080517)
                    ·
                      refine ⟨149045975658066566640097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 794911870176355022080517 149045975658066566640097)
                      ·
                        rfl

theorem cell23_290266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_290266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290266 prefixEnd_290266 := by exact prefixLift 290266
  have htrace : WordTrace (prefixWord ++ tailWord_290266) baseStart_290266 baseEnd_290266 := by
    simpa [prefixWord, tailWord_290266, baseEnd_290266] using wordTrace_append hprefix tailTrace_290266
  have hstable : (prefixWord ++ tailWord_290266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290266).length < 2 ^ (prefixWord ++ tailWord_290266).sum := by decide
  have hdescent : baseEnd_290266 < baseStart_290266 := by decide
  rcases family_descends (prefixWord ++ tailWord_290266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290277 : List Nat := [1, 3, 1, 5, 1, 2, 3, 2, 1, 1, 3]
def baseStart_290277 : Nat := 118140960795 + 290277 * 2 ^ 59
def prefixEnd_290277 : Nat := 4983230072969 + 3 ^ 40 * 290277 * 2
def baseEnd_290277 : Nat := 149051623945266023602547

theorem tailTrace_290277 : CollatzResearch.WordTrace tailWord_290277 prefixEnd_290277 149051623945266023602547 := by
  unfold tailWord_290277
  simp only [CollatzResearch.WordTrace]
  refine ⟨10587271969383479209813085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7058181312922319473208723 10587271969383479209813085)
  ·
    refine ⟨3970226988518804703679907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10587271969383479209813085 3970226988518804703679907)
    ·
      refine ⟨5955340482778207055519861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3970226988518804703679907 5955340482778207055519861)
      ·
        refine ⟨558313170260456911454987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5955340482778207055519861 558313170260456911454987)
        ·
          refine ⟨837469755390685367182481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558313170260456911454987 837469755390685367182481)
          ·
            refine ⟨628102316543014025386861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 837469755390685367182481 628102316543014025386861)
            ·
              refine ⟨235538368703630259520073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 628102316543014025386861 235538368703630259520073)
              ·
                refine ⟨176653776527722694640055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235538368703630259520073 176653776527722694640055)
                ·
                  refine ⟨264980664791584041960083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176653776527722694640055 264980664791584041960083)
                  ·
                    refine ⟨397470997187376062940125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 264980664791584041960083 397470997187376062940125)
                    ·
                      refine ⟨149051623945266023602547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 397470997187376062940125 149051623945266023602547)
                      ·
                        rfl

theorem cell23_290277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_290277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290277 prefixEnd_290277 := by exact prefixLift 290277
  have htrace : WordTrace (prefixWord ++ tailWord_290277) baseStart_290277 baseEnd_290277 := by
    simpa [prefixWord, tailWord_290277, baseEnd_290277] using wordTrace_append hprefix tailTrace_290277
  have hstable : (prefixWord ++ tailWord_290277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290277).length < 2 ^ (prefixWord ++ tailWord_290277).sum := by decide
  have hdescent : baseEnd_290277 < baseStart_290277 := by decide
  rcases family_descends (prefixWord ++ tailWord_290277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290279 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_290279 : Nat := 118140960795 + 290279 * 2 ^ 59
def prefixEnd_290279 : Nat := 4983230072969 + 3 ^ 40 * 290279 * 2
def baseEnd_290279 : Nat := 149052650906575015777537

theorem tailTrace_290279 : CollatzResearch.WordTrace tailWord_290279 prefixEnd_290279 149052650906575015777537 := by
  unfold tailWord_290279
  simp only [CollatzResearch.WordTrace]
  refine ⟨10587344915376233551385891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7058229943584155700923927 10587344915376233551385891)
  ·
    refine ⟨15881017373064350327078837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10587344915376233551385891 15881017373064350327078837)
    ·
      refine ⟨1488845378724782843163641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15881017373064350327078837 1488845378724782843163641)
      ·
        refine ⟨1116634034043587132372731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1488845378724782843163641 1116634034043587132372731)
        ·
          refine ⟨1674951051065380698559097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1116634034043587132372731 1674951051065380698559097)
          ·
            refine ⟨1256213288299035523919323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1674951051065380698559097 1256213288299035523919323)
            ·
              refine ⟨1884319932448553285878985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1256213288299035523919323 1884319932448553285878985)
              ·
                refine ⟨1413239949336414964409239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1884319932448553285878985 1413239949336414964409239)
                ·
                  refine ⟨2119859924004622446613859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1413239949336414964409239 2119859924004622446613859)
                  ·
                    refine ⟨3179789886006933669920789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2119859924004622446613859 3179789886006933669920789)
                    ·
                      refine ⟨149052650906575015777537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3179789886006933669920789 149052650906575015777537)
                      ·
                        rfl

theorem cell23_290279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_290279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290279 prefixEnd_290279 := by exact prefixLift 290279
  have htrace : WordTrace (prefixWord ++ tailWord_290279) baseStart_290279 baseEnd_290279 := by
    simpa [prefixWord, tailWord_290279, baseEnd_290279] using wordTrace_append hprefix tailTrace_290279
  have hstable : (prefixWord ++ tailWord_290279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290279).length < 2 ^ (prefixWord ++ tailWord_290279).sum := by decide
  have hdescent : baseEnd_290279 < baseStart_290279 := by decide
  rcases family_descends (prefixWord ++ tailWord_290279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290286 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_290286 : Nat := 118140960795 + 290286 * 2 ^ 59
def prefixEnd_290286 : Nat := 4983230072969 + 3 ^ 40 * 290286 * 2
def baseEnd_290286 : Nat := 149056245271156488390005

theorem tailTrace_290286 : CollatzResearch.WordTrace tailWord_290286 prefixEnd_290286 149056245271156488390005 := by
  unfold tailWord_290286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1323450028293859218361339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7058400150900582497927141 1323450028293859218361339)
  ·
    refine ⟨1985175042440788827542009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1323450028293859218361339 1985175042440788827542009)
    ·
      refine ⟨1488881281830591620656507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1985175042440788827542009 1488881281830591620656507)
      ·
        refine ⟨2233321922745887430984761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1488881281830591620656507 2233321922745887430984761)
        ·
          refine ⟨1674991442059415573238571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2233321922745887430984761 1674991442059415573238571)
          ·
            refine ⟨2512487163089123359857857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1674991442059415573238571 2512487163089123359857857)
            ·
              refine ⟨1884365372316842519893393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2512487163089123359857857 1884365372316842519893393)
              ·
                refine ⟨1413274029237631889920045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1884365372316842519893393 1413274029237631889920045)
                ·
                  refine ⟨529977760964111958720017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1413274029237631889920045 529977760964111958720017)
                  ·
                    refine ⟨397483320723083969040013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 529977760964111958720017 397483320723083969040013)
                    ·
                      refine ⟨149056245271156488390005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 397483320723083969040013 149056245271156488390005)
                      ·
                        rfl

theorem cell23_290286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_290286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290286 prefixEnd_290286 := by exact prefixLift 290286
  have htrace : WordTrace (prefixWord ++ tailWord_290286) baseStart_290286 baseEnd_290286 := by
    simpa [prefixWord, tailWord_290286, baseEnd_290286] using wordTrace_append hprefix tailTrace_290286
  have hstable : (prefixWord ++ tailWord_290286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290286).length < 2 ^ (prefixWord ++ tailWord_290286).sum := by decide
  have hdescent : baseEnd_290286 < baseStart_290286 := by decide
  rcases family_descends (prefixWord ++ tailWord_290286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290289 : List Nat := [1, 2, 2, 2, 3, 3, 2, 8]
def baseStart_290289 : Nat := 118140960795 + 290289 * 2 ^ 59
def prefixEnd_290289 : Nat := 4983230072969 + 3 ^ 40 * 290289 * 2
def baseEnd_290289 : Nat := 5520658730115554690833

theorem tailTrace_290289 : CollatzResearch.WordTrace tailWord_290289 prefixEnd_290289 5520658730115554690833 := by
  unfold tailWord_290289
  simp only [CollatzResearch.WordTrace]
  refine ⟨10587709645340005259249921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7058473096893336839499947 10587709645340005259249921)
  ·
    refine ⟨7940782234005003944437441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10587709645340005259249921 7940782234005003944437441)
    ·
      refine ⟨5955586675503752958328081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7940782234005003944437441 5955586675503752958328081)
      ·
        refine ⟨4466690006627814718746061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5955586675503752958328081 4466690006627814718746061)
        ·
          refine ⟨1675008752485430519529773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4466690006627814718746061 1675008752485430519529773)
          ·
            refine ⟨628128282182036444823665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1675008752485430519529773 628128282182036444823665)
            ·
              refine ⟨471096211636527333617749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 628128282182036444823665 471096211636527333617749)
              ·
                refine ⟨5520658730115554690833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 471096211636527333617749 5520658730115554690833)
                ·
                  rfl

theorem cell23_290289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 8].length) (baseStart_290289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290289 prefixEnd_290289 := by exact prefixLift 290289
  have htrace : WordTrace (prefixWord ++ tailWord_290289) baseStart_290289 baseEnd_290289 := by
    simpa [prefixWord, tailWord_290289, baseEnd_290289] using wordTrace_append hprefix tailTrace_290289
  have hstable : (prefixWord ++ tailWord_290289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290289).length < 2 ^ (prefixWord ++ tailWord_290289).sum := by decide
  have hdescent : baseEnd_290289 < baseStart_290289 := by decide
  rcases family_descends (prefixWord ++ tailWord_290289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290306 : List Nat := [3, 4, 1, 2, 1, 1, 2, 9]
def baseStart_290306 : Nat := 118140960795 + 290306 * 2 ^ 59
def prefixEnd_290306 : Nat := 4983230072969 + 3 ^ 40 * 290306 * 2
def baseEnd_290306 : Nat := 5520982032749867042219

theorem tailTrace_290306 : CollatzResearch.WordTrace tailWord_290306 prefixEnd_290306 5520982032749867042219 := by
  unfold tailWord_290306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2647082421569604290654693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7058886457518944775079181 2647082421569604290654693)
  ·
    refine ⟨496327954044300804497755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2647082421569604290654693 496327954044300804497755)
    ·
      refine ⟨744491931066451206746633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 496327954044300804497755 744491931066451206746633)
      ·
        refine ⟨558368948299838405059975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 744491931066451206746633 558368948299838405059975)
        ·
          refine ⟨837553422449757607589963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558368948299838405059975 837553422449757607589963)
          ·
            refine ⟨1256330133674636411384945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837553422449757607589963 1256330133674636411384945)
            ·
              refine ⟨942247600255977308538709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1256330133674636411384945 942247600255977308538709)
              ·
                refine ⟨5520982032749867042219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 942247600255977308538709 5520982032749867042219)
                ·
                  rfl

theorem cell23_290306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 9].length) (baseStart_290306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290306 prefixEnd_290306 := by exact prefixLift 290306
  have htrace : WordTrace (prefixWord ++ tailWord_290306) baseStart_290306 baseEnd_290306 := by
    simpa [prefixWord, tailWord_290306, baseEnd_290306] using wordTrace_append hprefix tailTrace_290306
  have hstable : (prefixWord ++ tailWord_290306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290306).length < 2 ^ (prefixWord ++ tailWord_290306).sum := by decide
  have hdescent : baseEnd_290306 < baseStart_290306 := by decide
  rcases family_descends (prefixWord ++ tailWord_290306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290350 : List Nat := [4, 1, 3, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_290350 : Nat := 118140960795 + 290350 * 2 ^ 59
def prefixEnd_290350 : Nat := 4983230072969 + 3 ^ 40 * 290350 * 2
def baseEnd_290350 : Nat := 149089108033044237989711

theorem tailTrace_290350 : CollatzResearch.WordTrace tailWord_290350 prefixEnd_290350 149089108033044237989711 := by
  unfold tailWord_290350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1323741812264876584652563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7059956332079341784813669 1323741812264876584652563)
  ·
    refine ⟨1985612718397314876978845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1323741812264876584652563 1985612718397314876978845)
    ·
      refine ⟨744604769398993078867067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1985612718397314876978845 744604769398993078867067)
      ·
        refine ⟨1116907154098489618300601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 744604769398993078867067 1116907154098489618300601)
        ·
          refine ⟨837680365573867213725451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1116907154098489618300601 837680365573867213725451)
          ·
            refine ⟨1256520548360800820588177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837680365573867213725451 1256520548360800820588177)
            ·
              refine ⟨942390411270600615441133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1256520548360800820588177 942390411270600615441133)
              ·
                refine ⟨353396404226475230790425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 942390411270600615441133 353396404226475230790425)
                ·
                  refine ⟨265047303169856423092819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353396404226475230790425 265047303169856423092819)
                  ·
                    refine ⟨397570954754784634639229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 265047303169856423092819 397570954754784634639229)
                    ·
                      refine ⟨149089108033044237989711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 397570954754784634639229 149089108033044237989711)
                      ·
                        rfl

theorem cell23_290350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_290350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290350 prefixEnd_290350 := by exact prefixLift 290350
  have htrace : WordTrace (prefixWord ++ tailWord_290350) baseStart_290350 baseEnd_290350 := by
    simpa [prefixWord, tailWord_290350, baseEnd_290350] using wordTrace_append hprefix tailTrace_290350
  have hstable : (prefixWord ++ tailWord_290350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290350).length < 2 ^ (prefixWord ++ tailWord_290350).sum := by decide
  have hdescent : baseEnd_290350 < baseStart_290350 := by decide
  rcases family_descends (prefixWord ++ tailWord_290350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290373 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 4, 2, 2]
def baseStart_290373 : Nat := 118140960795 + 290373 * 2 ^ 59
def prefixEnd_290373 : Nat := 4983230072969 + 3 ^ 40 * 290373 * 2
def baseEnd_290373 : Nat := 149100918088097648002105

theorem tailTrace_290373 : CollatzResearch.WordTrace tailWord_290373 prefixEnd_290373 149100918088097648002105 := by
  unfold tailWord_290373
  simp only [CollatzResearch.WordTrace]
  refine ⟨10590773377035687605307773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7060515584690458403538515 10590773377035687605307773)
  ·
    refine ⟨3971540016388382851990415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10590773377035687605307773 3971540016388382851990415)
    ·
      refine ⟨5957310024582574277985623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3971540016388382851990415 5957310024582574277985623)
      ·
        refine ⟨8935965036873861416978435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5957310024582574277985623 8935965036873861416978435)
        ·
          refine ⟨13403947555310792125467653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8935965036873861416978435 13403947555310792125467653)
          ·
            refine ⟨2513240166620773523525185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13403947555310792125467653 2513240166620773523525185)
            ·
              refine ⟨1884930124965580142643889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2513240166620773523525185 1884930124965580142643889)
              ·
                refine ⟨1413697593724185106982917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1884930124965580142643889 1413697593724185106982917)
                ·
                  refine ⟨265068298823284707559297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1413697593724185106982917 265068298823284707559297)
                  ·
                    refine ⟨198801224117463530669473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 265068298823284707559297 198801224117463530669473)
                    ·
                      refine ⟨149100918088097648002105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 198801224117463530669473 149100918088097648002105)
                      ·
                        rfl

theorem cell23_290373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 2, 2].length) (baseStart_290373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290373 prefixEnd_290373 := by exact prefixLift 290373
  have htrace : WordTrace (prefixWord ++ tailWord_290373) baseStart_290373 baseEnd_290373 := by
    simpa [prefixWord, tailWord_290373, baseEnd_290373] using wordTrace_append hprefix tailTrace_290373
  have hstable : (prefixWord ++ tailWord_290373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290373).length < 2 ^ (prefixWord ++ tailWord_290373).sum := by decide
  have hdescent : baseEnd_290373 < baseStart_290373 := by decide
  rcases family_descends (prefixWord ++ tailWord_290373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290386 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_290386 : Nat := 118140960795 + 290386 * 2 ^ 59
def prefixEnd_290386 : Nat := 4983230072969 + 3 ^ 40 * 290386 * 2
def baseEnd_290386 : Nat := 149107593336606097139545

theorem tailTrace_290386 : CollatzResearch.WordTrace tailWord_290386 prefixEnd_290386 149107593336606097139545 := by
  unfold tailWord_290386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2647811881497147706382753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7060831683992393883687341 2647811881497147706382753)
  ·
    refine ⟨1985858911122860779787065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2647811881497147706382753 1985858911122860779787065)
    ·
      refine ⟨1489394183342145584840299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1985858911122860779787065 1489394183342145584840299)
      ·
        refine ⟨2234091275013218377260449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1489394183342145584840299 2234091275013218377260449)
        ·
          refine ⟨1675568456259913782945337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2234091275013218377260449 1675568456259913782945337)
          ·
            refine ⟨1256676342194935337209003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1675568456259913782945337 1256676342194935337209003)
            ·
              refine ⟨1885014513292403005813505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1256676342194935337209003 1885014513292403005813505)
              ·
                refine ⟨1413760884969302254360129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1885014513292403005813505 1413760884969302254360129)
                ·
                  refine ⟨1060320663726976690770097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1413760884969302254360129 1060320663726976690770097)
                  ·
                    refine ⟨795240497795232518077573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1060320663726976690770097 795240497795232518077573)
                    ·
                      refine ⟨149107593336606097139545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 795240497795232518077573 149107593336606097139545)
                      ·
                        rfl

theorem cell23_290386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_290386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290386 prefixEnd_290386 := by exact prefixLift 290386
  have htrace : WordTrace (prefixWord ++ tailWord_290386) baseStart_290386 baseEnd_290386 := by
    simpa [prefixWord, tailWord_290386, baseEnd_290386] using wordTrace_append hprefix tailTrace_290386
  have hstable : (prefixWord ++ tailWord_290386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290386).length < 2 ^ (prefixWord ++ tailWord_290386).sum := by decide
  have hdescent : baseEnd_290386 < baseStart_290386 := by decide
  rcases family_descends (prefixWord ++ tailWord_290386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290396 : List Nat := [2, 2, 4, 1, 2, 1, 1, 3, 7]
def baseStart_290396 : Nat := 118140960795 + 290396 * 2 ^ 59
def prefixEnd_290396 : Nat := 4983230072969 + 3 ^ 40 * 290396 * 2
def baseEnd_290396 : Nat := 16568080904794562001611

theorem tailTrace_290396 : CollatzResearch.WordTrace tailWord_290396 prefixEnd_290396 16568080904794562001611 := by
  unfold tailWord_290396
  simp only [CollatzResearch.WordTrace]
  refine ⟨5295806127976181266697521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7061074837301575022263361 5295806127976181266697521)
  ·
    refine ⟨3971854595982135950023141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5295806127976181266697521 3971854595982135950023141)
    ·
      refine ⟨744722736746650490629339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3971854595982135950023141 744722736746650490629339)
      ·
        refine ⟨1117084105119975735944009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 744722736746650490629339 1117084105119975735944009)
        ·
          refine ⟨837813078839981801958007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1117084105119975735944009 837813078839981801958007)
          ·
            refine ⟨1256719618259972702937011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837813078839981801958007 1256719618259972702937011)
            ·
              refine ⟨1885079427389959054405517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1256719618259972702937011 1885079427389959054405517)
              ·
                refine ⟨706904785271234645402069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1885079427389959054405517 706904785271234645402069)
                ·
                  refine ⟨16568080904794562001611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 706904785271234645402069 16568080904794562001611)
                  ·
                    rfl

theorem cell23_290396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 7].length) (baseStart_290396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290396 prefixEnd_290396 := by exact prefixLift 290396
  have htrace : WordTrace (prefixWord ++ tailWord_290396) baseStart_290396 baseEnd_290396 := by
    simpa [prefixWord, tailWord_290396, baseEnd_290396] using wordTrace_append hprefix tailTrace_290396
  have hstable : (prefixWord ++ tailWord_290396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290396).length < 2 ^ (prefixWord ++ tailWord_290396).sum := by decide
  have hdescent : baseEnd_290396 < baseStart_290396 := by decide
  rcases family_descends (prefixWord ++ tailWord_290396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290409 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 1, 7]
def baseStart_290409 : Nat := 118140960795 + 290409 * 2 ^ 59
def prefixEnd_290409 : Nat := 4983230072969 + 3 ^ 40 * 290409 * 2
def baseEnd_290409 : Nat := 49706467797219835717313

theorem tailTrace_290409 : CollatzResearch.WordTrace tailWord_290409 prefixEnd_290409 49706467797219835717313 := by
  unfold tailWord_290409
  simp only [CollatzResearch.WordTrace]
  refine ⟨10592086404905265753618281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7061390936603510502412187 10592086404905265753618281)
  ·
    refine ⟨7944064803678949315213711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10592086404905265753618281 7944064803678949315213711)
    ·
      refine ⟨11916097205518423972820567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7944064803678949315213711 11916097205518423972820567)
      ·
        refine ⟨17874145808277635959230851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11916097205518423972820567 17874145808277635959230851)
        ·
          refine ⟨26811218712416453938846277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17874145808277635959230851 26811218712416453938846277)
          ·
            refine ⟨5027103508578085113533677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26811218712416453938846277 5027103508578085113533677)
            ·
              refine ⟨1885163815716781917575129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5027103508578085113533677 1885163815716781917575129)
              ·
                refine ⟨1413872861787586438181347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1885163815716781917575129 1413872861787586438181347)
                ·
                  refine ⟨2120809292681379657272021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1413872861787586438181347 2120809292681379657272021)
                  ·
                    refine ⟨49706467797219835717313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2120809292681379657272021 49706467797219835717313)
                    ·
                      rfl

theorem cell23_290409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 7].length) (baseStart_290409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290409 prefixEnd_290409 := by exact prefixLift 290409
  have htrace : WordTrace (prefixWord ++ tailWord_290409) baseStart_290409 baseEnd_290409 := by
    simpa [prefixWord, tailWord_290409, baseEnd_290409] using wordTrace_append hprefix tailTrace_290409
  have hstable : (prefixWord ++ tailWord_290409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290409).length < 2 ^ (prefixWord ++ tailWord_290409).sum := by decide
  have hdescent : baseEnd_290409 < baseStart_290409 := by decide
  rcases family_descends (prefixWord ++ tailWord_290409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290449 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 5]
def baseStart_290449 : Nat := 118140960795 + 290449 * 2 ^ 59
def prefixEnd_290449 : Nat := 4983230072969 + 3 ^ 40 * 290449 * 2
def baseEnd_290449 : Nat := 149139942617839350651755

theorem tailTrace_290449 : CollatzResearch.WordTrace tailWord_290449 prefixEnd_290449 149139942617839350651755 := by
  unfold tailWord_290449
  simp only [CollatzResearch.WordTrace]
  refine ⟨10593545324760352585074401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7062363549840235056716267 10593545324760352585074401)
  ·
    refine ⟨7945158993570264438805801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10593545324760352585074401 7945158993570264438805801)
    ·
      refine ⟨5958869245177698329104351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7945158993570264438805801 5958869245177698329104351)
      ·
        refine ⟨8938303867766547493656527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5958869245177698329104351 8938303867766547493656527)
        ·
          refine ⟨13407455801649821240484791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8938303867766547493656527 13407455801649821240484791)
          ·
            refine ⟨20111183702474731860727187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13407455801649821240484791 20111183702474731860727187)
            ·
              refine ⟨30166775553712097791090781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20111183702474731860727187 30166775553712097791090781)
              ·
                refine ⟨11312540832642036671659043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30166775553712097791090781 11312540832642036671659043)
                ·
                  refine ⟨16968811248963055007488565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11312540832642036671659043 16968811248963055007488565)
                  ·
                    refine ⟨1590826054590286406952053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16968811248963055007488565 1590826054590286406952053)
                    ·
                      refine ⟨149139942617839350651755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1590826054590286406952053 149139942617839350651755)
                      ·
                        rfl

theorem cell23_290449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_290449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290449 prefixEnd_290449 := by exact prefixLift 290449
  have htrace : WordTrace (prefixWord ++ tailWord_290449) baseStart_290449 baseEnd_290449 := by
    simpa [prefixWord, tailWord_290449, baseEnd_290449] using wordTrace_append hprefix tailTrace_290449
  have hstable : (prefixWord ++ tailWord_290449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290449).length < 2 ^ (prefixWord ++ tailWord_290449).sum := by decide
  have hdescent : baseEnd_290449 < baseStart_290449 := by decide
  rcases family_descends (prefixWord ++ tailWord_290449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290483 : List Nat := [1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 3]
def baseStart_290483 : Nat := 118140960795 + 290483 * 2 ^ 59
def prefixEnd_290483 : Nat := 4983230072969 + 3 ^ 40 * 290483 * 2
def baseEnd_290483 : Nat := 149157400960092217626599

theorem tailTrace_290483 : CollatzResearch.WordTrace tailWord_290483 prefixEnd_290483 149157400960092217626599 := by
  unfold tailWord_290483
  simp only [CollatzResearch.WordTrace]
  refine ⟨10594785406637176391812103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7063190271091450927874735 10594785406637176391812103)
  ·
    refine ⟨15892178109955764587718155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10594785406637176391812103 15892178109955764587718155)
    ·
      refine ⟨23838267164933646881577233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15892178109955764587718155 23838267164933646881577233)
      ·
        refine ⟨17878700373700235161182925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23838267164933646881577233 17878700373700235161182925)
        ·
          refine ⟨6704512640137588185443597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17878700373700235161182925 6704512640137588185443597)
          ·
            refine ⟨2514192240051595569541349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6704512640137588185443597 2514192240051595569541349)
            ·
              refine ⟨471411045009674169289003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2514192240051595569541349 471411045009674169289003)
              ·
                refine ⟨707116567514511253933505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471411045009674169289003 707116567514511253933505)
                ·
                  refine ⟨530337425635883440450129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 707116567514511253933505 530337425635883440450129)
                  ·
                    refine ⟨397753069226912580337597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 530337425635883440450129 397753069226912580337597)
                    ·
                      refine ⟨149157400960092217626599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 397753069226912580337597 149157400960092217626599)
                      ·
                        rfl

theorem cell23_290483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 3].length) (baseStart_290483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290483 prefixEnd_290483 := by exact prefixLift 290483
  have htrace : WordTrace (prefixWord ++ tailWord_290483) baseStart_290483 baseEnd_290483 := by
    simpa [prefixWord, tailWord_290483, baseEnd_290483] using wordTrace_append hprefix tailTrace_290483
  have hstable : (prefixWord ++ tailWord_290483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290483).length < 2 ^ (prefixWord ++ tailWord_290483).sum := by decide
  have hdescent : baseEnd_290483 < baseStart_290483 := by decide
  rcases family_descends (prefixWord ++ tailWord_290483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290498 : List Nat := [3, 5, 1, 2, 2, 1, 2, 2, 5]
def baseStart_290498 : Nat := 118140960795 + 290498 * 2 ^ 59
def prefixEnd_290498 : Nat := 4983230072969 + 3 ^ 40 * 290498 * 2
def baseEnd_290498 : Nat := 16573900352212184326559

theorem tailTrace_290498 : CollatzResearch.WordTrace tailWord_290498 prefixEnd_290498 16573900352212184326559 := by
  unfold tailWord_290498
  simp only [CollatzResearch.WordTrace]
  refine ⟨2648833125395708488402037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7063555001055222635738765 2648833125395708488402037)
  ·
    refine ⟨248328105505847670787691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2648833125395708488402037 248328105505847670787691)
    ·
      refine ⟨372492158258771506181537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248328105505847670787691 372492158258771506181537)
      ·
        refine ⟨279369118694078629636153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372492158258771506181537 279369118694078629636153)
        ·
          refine ⟨209526839020558972227115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279369118694078629636153 209526839020558972227115)
          ·
            refine ⟨314290258530838458340673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209526839020558972227115 314290258530838458340673)
            ·
              refine ⟨235717693898128843755505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314290258530838458340673 235717693898128843755505)
              ·
                refine ⟨176788270423596632816629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235717693898128843755505 176788270423596632816629)
                ·
                  refine ⟨16573900352212184326559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 176788270423596632816629 16573900352212184326559)
                  ·
                    rfl

theorem cell23_290498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_290498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290498 prefixEnd_290498 := by exact prefixLift 290498
  have htrace : WordTrace (prefixWord ++ tailWord_290498) baseStart_290498 baseEnd_290498 := by
    simpa [prefixWord, tailWord_290498, baseEnd_290498] using wordTrace_append hprefix tailTrace_290498
  have hstable : (prefixWord ++ tailWord_290498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290498).length < 2 ^ (prefixWord ++ tailWord_290498).sum := by decide
  have hdescent : baseEnd_290498 < baseStart_290498 := by decide
  rcases family_descends (prefixWord ++ tailWord_290498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290533 : List Nat := [1, 3, 1, 4, 1, 1, 2, 4, 1, 5]
def baseStart_290533 : Nat := 118140960795 + 290533 * 2 ^ 59
def prefixEnd_290533 : Nat := 4983230072969 + 3 ^ 40 * 290533 * 2
def baseEnd_290533 : Nat := 49727691664272340667123

theorem tailTrace_290533 : CollatzResearch.WordTrace tailWord_290533 prefixEnd_290533 49727691664272340667123 := by
  unfold tailWord_290533
  simp only [CollatzResearch.WordTrace]
  refine ⟨10596609056456034931132253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7064406037637356620754835 10596609056456034931132253)
  ·
    refine ⟨3973728396171013099174595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10596609056456034931132253 3973728396171013099174595)
    ·
      refine ⟨5960592594256519648761893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3973728396171013099174595 5960592594256519648761893)
      ·
        refine ⟨1117611111423097434142855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5960592594256519648761893 1117611111423097434142855)
        ·
          refine ⟨1676416667134646151214283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1117611111423097434142855 1676416667134646151214283)
          ·
            refine ⟨2514625000701969226821425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1676416667134646151214283 2514625000701969226821425)
            ·
              refine ⟨1885968750526476920116069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2514625000701969226821425 1885968750526476920116069)
              ·
                refine ⟨353619140723714422521763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1885968750526476920116069 353619140723714422521763)
                ·
                  refine ⟨530428711085571633782645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353619140723714422521763 530428711085571633782645)
                  ·
                    refine ⟨49727691664272340667123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 530428711085571633782645 49727691664272340667123)
                    ·
                      rfl

theorem cell23_290533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_290533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290533 prefixEnd_290533 := by exact prefixLift 290533
  have htrace : WordTrace (prefixWord ++ tailWord_290533) baseStart_290533 baseEnd_290533 := by
    simpa [prefixWord, tailWord_290533, baseEnd_290533] using wordTrace_append hprefix tailTrace_290533
  have hstable : (prefixWord ++ tailWord_290533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290533).length < 2 ^ (prefixWord ++ tailWord_290533).sum := by decide
  have hdescent : baseEnd_290533 < baseStart_290533 := by decide
  rcases family_descends (prefixWord ++ tailWord_290533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290540 : List Nat := [2, 2, 1, 1, 2, 2, 5, 1, 2, 3, 2]
def baseStart_290540 : Nat := 118140960795 + 290540 * 2 ^ 59
def prefixEnd_290540 : Nat := 4983230072969 + 3 ^ 40 * 290540 * 2
def baseEnd_290540 : Nat := 149186669357398494613837

theorem tailTrace_290540 : CollatzResearch.WordTrace tailWord_290540 prefixEnd_290540 149186669357398494613837 := by
  unfold tailWord_290540
  simp only [CollatzResearch.WordTrace]
  refine ⟨5298432183715337563318537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7064576244953783417758049 5298432183715337563318537)
  ·
    refine ⟨3973824137786503172488903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5298432183715337563318537 3973824137786503172488903)
    ·
      refine ⟨5960736206679754758733355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3973824137786503172488903 5960736206679754758733355)
      ·
        refine ⟨8941104310019632138100033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5960736206679754758733355 8941104310019632138100033)
        ·
          refine ⟨6705828232514724103575025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8941104310019632138100033 6705828232514724103575025)
          ·
            refine ⟨5029371174386043077681269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6705828232514724103575025 5029371174386043077681269)
            ·
              refine ⟨471503547598691538532619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5029371174386043077681269 471503547598691538532619)
              ·
                refine ⟨707255321398037307798929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471503547598691538532619 707255321398037307798929)
                ·
                  refine ⟨530441491048527980849197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 707255321398037307798929 530441491048527980849197)
                  ·
                    refine ⟨198915559143197992818449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 530441491048527980849197 198915559143197992818449)
                    ·
                      refine ⟨149186669357398494613837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 198915559143197992818449 149186669357398494613837)
                      ·
                        rfl

theorem cell23_290540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 3, 2].length) (baseStart_290540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290540 prefixEnd_290540 := by exact prefixLift 290540
  have htrace : WordTrace (prefixWord ++ tailWord_290540) baseStart_290540 baseEnd_290540 := by
    simpa [prefixWord, tailWord_290540, baseEnd_290540] using wordTrace_append hprefix tailTrace_290540
  have hstable : (prefixWord ++ tailWord_290540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290540).length < 2 ^ (prefixWord ++ tailWord_290540).sum := by decide
  have hdescent : baseEnd_290540 < baseStart_290540 := by decide
  rcases family_descends (prefixWord ++ tailWord_290540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290550 : List Nat := [5, 1, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_290550 : Nat := 118140960795 + 290550 * 2 ^ 59
def prefixEnd_290550 : Nat := 4983230072969 + 3 ^ 40 * 290550 * 2
def baseEnd_290550 : Nat := 49730601387981151829597

theorem tailTrace_290550 : CollatzResearch.WordTrace tailWord_290550 prefixEnd_290550 49730601387981151829597 := by
  unfold tailWord_290550
  simp only [CollatzResearch.WordTrace]
  refine ⟨662326818587152927156319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7064819398262964556334069 662326818587152927156319)
  ·
    refine ⟨993490227880729390734479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 662326818587152927156319 993490227880729390734479)
    ·
      refine ⟨1490235341821094086101719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 993490227880729390734479 1490235341821094086101719)
      ·
        refine ⟨2235353012731641129152579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1490235341821094086101719 2235353012731641129152579)
        ·
          refine ⟨3353029519097461693728869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2235353012731641129152579 3353029519097461693728869)
          ·
            refine ⟨628693034830774067574163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3353029519097461693728869 628693034830774067574163)
            ·
              refine ⟨943039552246161101361245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628693034830774067574163 943039552246161101361245)
              ·
                refine ⟨353639832092310413010467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 943039552246161101361245 353639832092310413010467)
                ·
                  refine ⟨530459748138465619515701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353639832092310413010467 530459748138465619515701)
                  ·
                    refine ⟨49730601387981151829597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 530459748138465619515701 49730601387981151829597)
                    ·
                      rfl

theorem cell23_290550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_290550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290550 prefixEnd_290550 := by exact prefixLift 290550
  have htrace : WordTrace (prefixWord ++ tailWord_290550) baseStart_290550 baseEnd_290550 := by
    simpa [prefixWord, tailWord_290550, baseEnd_290550] using wordTrace_append hprefix tailTrace_290550
  have hstable : (prefixWord ++ tailWord_290550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290550).length < 2 ^ (prefixWord ++ tailWord_290550).sum := by decide
  have hdescent : baseEnd_290550 < baseStart_290550 := by decide
  rcases family_descends (prefixWord ++ tailWord_290550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290583 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 6]
def baseStart_290583 : Nat := 118140960795 + 290583 * 2 ^ 59
def prefixEnd_290583 : Nat := 4983230072969 + 3 ^ 40 * 290583 * 2
def baseEnd_290583 : Nat := 149208749025541826376139

theorem tailTrace_290583 : CollatzResearch.WordTrace tailWord_290583 prefixEnd_290583 149208749025541826376139 := by
  unfold tailWord_290583
  simp only [CollatzResearch.WordTrace]
  refine ⟨10598432706274893470452403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7065621804183262313634935 10598432706274893470452403)
  ·
    refine ⟨15897649059412340205678605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10598432706274893470452403 15897649059412340205678605)
    ·
      refine ⟨5961618397279627577129477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15897649059412340205678605 5961618397279627577129477)
      ·
        refine ⟨1117803449489930170711777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5961618397279627577129477 1117803449489930170711777)
        ·
          refine ⟨838352587117447628033833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1117803449489930170711777 838352587117447628033833)
          ·
            refine ⟨628764440338085721025375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 838352587117447628033833 628764440338085721025375)
            ·
              refine ⟨943146660507128581538063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628764440338085721025375 943146660507128581538063)
              ·
                refine ⟨1414719990760692872307095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 943146660507128581538063 1414719990760692872307095)
                ·
                  refine ⟨2122079986141039308460643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1414719990760692872307095 2122079986141039308460643)
                  ·
                    refine ⟨3183119979211558962690965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2122079986141039308460643 3183119979211558962690965)
                    ·
                      refine ⟨149208749025541826376139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3183119979211558962690965 149208749025541826376139)
                      ·
                        rfl

theorem cell23_290583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_290583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290583 prefixEnd_290583 := by exact prefixLift 290583
  have htrace : WordTrace (prefixWord ++ tailWord_290583) baseStart_290583 baseEnd_290583 := by
    simpa [prefixWord, tailWord_290583, baseEnd_290583] using wordTrace_append hprefix tailTrace_290583
  have hstable : (prefixWord ++ tailWord_290583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290583).length < 2 ^ (prefixWord ++ tailWord_290583).sum := by decide
  have hdescent : baseEnd_290583 < baseStart_290583 := by decide
  rcases family_descends (prefixWord ++ tailWord_290583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290593 : List Nat := [1, 2, 3, 2, 1, 3, 4, 7]
def baseStart_290593 : Nat := 118140960795 + 290593 * 2 ^ 59
def prefixEnd_290593 : Nat := 4983230072969 + 3 ^ 40 * 290593 * 2
def baseEnd_290593 : Nat := 5526440141929140268559

theorem tailTrace_290593 : CollatzResearch.WordTrace tailWord_290593 prefixEnd_290593 5526440141929140268559 := by
  unfold tailWord_290593
  simp only [CollatzResearch.WordTrace]
  refine ⟨10598797436238665178316433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7065864957492443452210955 10598797436238665178316433)
  ·
    refine ⟨7949098077178998883737325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10598797436238665178316433 7949098077178998883737325)
    ·
      refine ⟨2980911778942124581401497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7949098077178998883737325 2980911778942124581401497)
      ·
        refine ⟨2235683834206593436051123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2980911778942124581401497 2235683834206593436051123)
        ·
          refine ⟨3353525751309890154076685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2235683834206593436051123 3353525751309890154076685)
          ·
            refine ⟨1257572156741208807778757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3353525751309890154076685 1257572156741208807778757)
            ·
              refine ⟨235794779388976651458517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1257572156741208807778757 235794779388976651458517)
              ·
                refine ⟨5526440141929140268559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 235794779388976651458517 5526440141929140268559)
                ·
                  rfl

theorem cell23_290593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 7].length) (baseStart_290593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290593 prefixEnd_290593 := by exact prefixLift 290593
  have htrace : WordTrace (prefixWord ++ tailWord_290593) baseStart_290593 baseEnd_290593 := by
    simpa [prefixWord, tailWord_290593, baseEnd_290593] using wordTrace_append hprefix tailTrace_290593
  have hstable : (prefixWord ++ tailWord_290593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290593).length < 2 ^ (prefixWord ++ tailWord_290593).sum := by decide
  have hdescent : baseEnd_290593 < baseStart_290593 := by decide
  rcases family_descends (prefixWord ++ tailWord_290593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290604 : List Nat := [2, 2, 1, 1, 1, 5, 3, 3, 1, 2, 2]
def baseStart_290604 : Nat := 118140960795 + 290604 * 2 ^ 59
def prefixEnd_290604 : Nat := 4983230072969 + 3 ^ 40 * 290604 * 2
def baseEnd_290604 : Nat := 149219532119286244213543

theorem tailTrace_290604 : CollatzResearch.WordTrace tailWord_290604 prefixEnd_290604 149219532119286244213543 := by
  unfold tailWord_290604
  simp only [CollatzResearch.WordTrace]
  refine ⟨5299599319599407028483433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7066132426132542704644577 5299599319599407028483433)
  ·
    refine ⟨3974699489699555271362575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5299599319599407028483433 3974699489699555271362575)
    ·
      refine ⟨5962049234549332907043863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3974699489699555271362575 5962049234549332907043863)
      ·
        refine ⟨8943073851823999360565795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5962049234549332907043863 8943073851823999360565795)
        ·
          refine ⟨13414610777735999040848693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8943073851823999360565795 13414610777735999040848693)
          ·
            refine ⟨1257619760412749910079565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13414610777735999040848693 1257619760412749910079565)
            ·
              refine ⟨471607410154781216279837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1257619760412749910079565 471607410154781216279837)
              ·
                refine ⟨176852778808042956104939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 471607410154781216279837 176852778808042956104939)
                ·
                  refine ⟨265279168212064434157409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176852778808042956104939 265279168212064434157409)
                  ·
                    refine ⟨198959376159048325618057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 265279168212064434157409 198959376159048325618057)
                    ·
                      refine ⟨149219532119286244213543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 198959376159048325618057 149219532119286244213543)
                      ·
                        rfl

theorem cell23_290604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 1, 2, 2].length) (baseStart_290604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290604 prefixEnd_290604 := by exact prefixLift 290604
  have htrace : WordTrace (prefixWord ++ tailWord_290604) baseStart_290604 baseEnd_290604 := by
    simpa [prefixWord, tailWord_290604, baseEnd_290604] using wordTrace_append hprefix tailTrace_290604
  have hstable : (prefixWord ++ tailWord_290604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290604).length < 2 ^ (prefixWord ++ tailWord_290604).sum := by decide
  have hdescent : baseEnd_290604 < baseStart_290604 := by decide
  rcases family_descends (prefixWord ++ tailWord_290604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290620 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 4, 1, 3]
def baseStart_290620 : Nat := 118140960795 + 290620 * 2 ^ 59
def prefixEnd_290620 : Nat := 4983230072969 + 3 ^ 40 * 290620 * 2
def baseEnd_290620 : Nat := 149227747809758181613469

theorem tailTrace_290620 : CollatzResearch.WordTrace tailWord_290620 prefixEnd_290620 149227747809758181613469 := by
  unfold tailWord_290620
  simp only [CollatzResearch.WordTrace]
  refine ⟨5299891103570424394774657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7066521471427232526366209 5299891103570424394774657)
  ·
    refine ⟨3974918327677818296080993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5299891103570424394774657 3974918327677818296080993)
    ·
      refine ⟨2981188745758363722060745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3974918327677818296080993 2981188745758363722060745)
      ·
        refine ⟨2235891559318772791545559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2981188745758363722060745 2235891559318772791545559)
        ·
          refine ⟨3353837338978159187318339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2235891559318772791545559 3353837338978159187318339)
          ·
            refine ⟨5030756008467238780977509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3353837338978159187318339 5030756008467238780977509)
            ·
              refine ⟨943266751587607271433283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5030756008467238780977509 943266751587607271433283)
              ·
                refine ⟨1414900127381410907149925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 943266751587607271433283 1414900127381410907149925)
                ·
                  refine ⟨265293773884014545090611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1414900127381410907149925 265293773884014545090611)
                  ·
                    refine ⟨397940660826021817635917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 265293773884014545090611 397940660826021817635917)
                    ·
                      refine ⟨149227747809758181613469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 397940660826021817635917 149227747809758181613469)
                      ·
                        rfl

theorem cell23_290620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_290620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290620 prefixEnd_290620 := by exact prefixLift 290620
  have htrace : WordTrace (prefixWord ++ tailWord_290620) baseStart_290620 baseEnd_290620 := by
    simpa [prefixWord, tailWord_290620, baseEnd_290620] using wordTrace_append hprefix tailTrace_290620
  have hstable : (prefixWord ++ tailWord_290620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290620).length < 2 ^ (prefixWord ++ tailWord_290620).sum := by decide
  have hdescent : baseEnd_290620 < baseStart_290620 := by decide
  rcases family_descends (prefixWord ++ tailWord_290620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290647 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 3, 3, 2]
def baseStart_290647 : Nat := 118140960795 + 290647 * 2 ^ 59
def prefixEnd_290647 : Nat := 4983230072969 + 3 ^ 40 * 290647 * 2
def baseEnd_290647 : Nat := 149241611787429575975845

theorem tailTrace_290647 : CollatzResearch.WordTrace tailWord_290647 prefixEnd_290647 149241611787429575975845 := by
  unfold tailWord_290647
  simp only [CollatzResearch.WordTrace]
  refine ⟨10600766978043032400782195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7067177985362021600521463 10600766978043032400782195)
  ·
    refine ⟨15901150467064548601173293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10600766978043032400782195 15901150467064548601173293)
    ·
      refine ⟨5962931425149205725439985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15901150467064548601173293 5962931425149205725439985)
      ·
        refine ⟨4472198568861904294079989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5962931425149205725439985 4472198568861904294079989)
        ·
          refine ⟨419268615830803527569999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4472198568861904294079989 419268615830803527569999)
          ·
            refine ⟨628902923746205291354999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419268615830803527569999 628902923746205291354999)
            ·
              refine ⟨943354385619307937032499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628902923746205291354999 943354385619307937032499)
              ·
                refine ⟨1415031578428961905548749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 943354385619307937032499 1415031578428961905548749)
                ·
                  refine ⟨530636841910860714580781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1415031578428961905548749 530636841910860714580781)
                  ·
                    refine ⟨198988815716572767967793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 530636841910860714580781 198988815716572767967793)
                    ·
                      refine ⟨149241611787429575975845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 198988815716572767967793 149241611787429575975845)
                      ·
                        rfl

theorem cell23_290647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_290647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290647 prefixEnd_290647 := by exact prefixLift 290647
  have htrace : WordTrace (prefixWord ++ tailWord_290647) baseStart_290647 baseEnd_290647 := by
    simpa [prefixWord, tailWord_290647, baseEnd_290647] using wordTrace_append hprefix tailTrace_290647
  have hstable : (prefixWord ++ tailWord_290647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290647).length < 2 ^ (prefixWord ++ tailWord_290647).sum := by decide
  have hdescent : baseEnd_290647 < baseStart_290647 := by decide
  rcases family_descends (prefixWord ++ tailWord_290647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290663 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_290663 : Nat := 118140960795 + 290663 * 2 ^ 59
def prefixEnd_290663 : Nat := 4983230072969 + 3 ^ 40 * 290663 * 2
def baseEnd_290663 : Nat := 149249827477901513375771

theorem tailTrace_290663 : CollatzResearch.WordTrace tailWord_290663 prefixEnd_290663 149249827477901513375771 := by
  unfold tailWord_290663
  simp only [CollatzResearch.WordTrace]
  refine ⟨10601350545985067133364643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7067567030656711422243095 10601350545985067133364643)
  ·
    refine ⟨15902025818977600700046965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10601350545985067133364643 15902025818977600700046965)
    ·
      refine ⟨1490814920529150065629403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15902025818977600700046965 1490814920529150065629403)
      ·
        refine ⟨2236222380793725098444105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1490814920529150065629403 2236222380793725098444105)
        ·
          refine ⟨1677166785595293823833079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2236222380793725098444105 1677166785595293823833079)
          ·
            refine ⟨2515750178392940735749619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1677166785595293823833079 2515750178392940735749619)
            ·
              refine ⟨3773625267589411103624429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2515750178392940735749619 3773625267589411103624429)
              ·
                refine ⟨1415109475346029163859161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3773625267589411103624429 1415109475346029163859161)
                ·
                  refine ⟨1061332106509521872894371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1415109475346029163859161 1061332106509521872894371)
                  ·
                    refine ⟨1591998159764282809341557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1061332106509521872894371 1591998159764282809341557)
                    ·
                      refine ⟨149249827477901513375771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1591998159764282809341557 149249827477901513375771)
                      ·
                        rfl

theorem cell23_290663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_290663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290663 prefixEnd_290663 := by exact prefixLift 290663
  have htrace : WordTrace (prefixWord ++ tailWord_290663) baseStart_290663 baseEnd_290663 := by
    simpa [prefixWord, tailWord_290663, baseEnd_290663] using wordTrace_append hprefix tailTrace_290663
  have hstable : (prefixWord ++ tailWord_290663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290663).length < 2 ^ (prefixWord ++ tailWord_290663).sum := by decide
  have hdescent : baseEnd_290663 < baseStart_290663 := by decide
  rcases family_descends (prefixWord ++ tailWord_290663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290664 : List Nat := [2, 1, 4, 2, 1, 1, 5, 1, 1, 3, 2]
def baseStart_290664 : Nat := 118140960795 + 290664 * 2 ^ 59
def prefixEnd_290664 : Nat := 4983230072969 + 3 ^ 40 * 290664 * 2
def baseEnd_290664 : Nat := 149250340958556009463267

theorem tailTrace_290664 : CollatzResearch.WordTrace tailWord_290664 prefixEnd_290664 149250340958556009463267 := by
  unfold tailWord_290664
  simp only [CollatzResearch.WordTrace]
  refine ⟨5300693509490722152075523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7067591345987629536100697 5300693509490722152075523)
  ·
    refine ⟨7951040264236083228113285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5300693509490722152075523 7951040264236083228113285)
    ·
      refine ⟨1490820049544265605271241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7951040264236083228113285 1490820049544265605271241)
      ·
        refine ⟨1118115037158199203953431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1490820049544265605271241 1118115037158199203953431)
        ·
          refine ⟨1677172555737298805930147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118115037158199203953431 1677172555737298805930147)
          ·
            refine ⟨2515758833605948208895221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1677172555737298805930147 2515758833605948208895221)
            ·
              refine ⟨235852390650557644583927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2515758833605948208895221 235852390650557644583927)
              ·
                refine ⟨353778585975836466875891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235852390650557644583927 353778585975836466875891)
                ·
                  refine ⟨530667878963754700313837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353778585975836466875891 530667878963754700313837)
                  ·
                    refine ⟨199000454611408012617689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 530667878963754700313837 199000454611408012617689)
                    ·
                      refine ⟨149250340958556009463267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 199000454611408012617689 149250340958556009463267)
                      ·
                        rfl

theorem cell23_290664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_290664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290664 prefixEnd_290664 := by exact prefixLift 290664
  have htrace : WordTrace (prefixWord ++ tailWord_290664) baseStart_290664 baseEnd_290664 := by
    simpa [prefixWord, tailWord_290664, baseEnd_290664] using wordTrace_append hprefix tailTrace_290664
  have hstable : (prefixWord ++ tailWord_290664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290664).length < 2 ^ (prefixWord ++ tailWord_290664).sum := by decide
  have hdescent : baseEnd_290664 < baseStart_290664 := by decide
  rcases family_descends (prefixWord ++ tailWord_290664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290673 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 2, 2, 4]
def baseStart_290673 : Nat := 118140960795 + 290673 * 2 ^ 59
def prefixEnd_290673 : Nat := 4983230072969 + 3 ^ 40 * 290673 * 2
def baseEnd_290673 : Nat := 149254962284446474250725

theorem tailTrace_290673 : CollatzResearch.WordTrace tailWord_290673 prefixEnd_290673 149254962284446474250725 := by
  unfold tailWord_290673
  simp only [CollatzResearch.WordTrace]
  refine ⟨10601715275948838841228673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7067810183965892560819115 10601715275948838841228673)
  ·
    refine ⟨7951286456961629130921505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10601715275948838841228673 7951286456961629130921505)
    ·
      refine ⟨5963464842721221848191129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7951286456961629130921505 5963464842721221848191129)
      ·
        refine ⟨4472598632040916386143347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5963464842721221848191129 4472598632040916386143347)
        ·
          refine ⟨6708897948061374579215021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4472598632040916386143347 6708897948061374579215021)
          ·
            refine ⟨2515836730523015467205633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6708897948061374579215021 2515836730523015467205633)
            ·
              refine ⟨1886877547892261600404225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2515836730523015467205633 1886877547892261600404225)
              ·
                refine ⟨1415158160919196200303169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1886877547892261600404225 1415158160919196200303169)
                ·
                  refine ⟨1061368620689397150227377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1415158160919196200303169 1061368620689397150227377)
                  ·
                    refine ⟨796026465517047862670533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1061368620689397150227377 796026465517047862670533)
                    ·
                      refine ⟨149254962284446474250725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 796026465517047862670533 149254962284446474250725)
                      ·
                        rfl

theorem cell23_290673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_290673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290673 prefixEnd_290673 := by exact prefixLift 290673
  have htrace : WordTrace (prefixWord ++ tailWord_290673) baseStart_290673 baseEnd_290673 := by
    simpa [prefixWord, tailWord_290673, baseEnd_290673] using wordTrace_append hprefix tailTrace_290673
  have hstable : (prefixWord ++ tailWord_290673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290673).length < 2 ^ (prefixWord ++ tailWord_290673).sum := by decide
  have hdescent : baseEnd_290673 < baseStart_290673 := by decide
  rcases family_descends (prefixWord ++ tailWord_290673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290717 : List Nat := [1, 4, 2, 1, 2, 3, 2, 3, 5]
def baseStart_290717 : Nat := 118140960795 + 290717 * 2 ^ 59
def prefixEnd_290717 : Nat := 4983230072969 + 3 ^ 40 * 290717 * 2
def baseEnd_290717 : Nat := 16586395048138255788947

theorem tailTrace_290717 : CollatzResearch.WordTrace tailWord_290717 prefixEnd_290717 16586395048138255788947 := by
  unfold tailWord_290717
  simp only [CollatzResearch.WordTrace]
  refine ⟨10603320087789434355830405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7068880058526289570553603 10603320087789434355830405)
  ·
    refine ⟨1988122516460518941718201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10603320087789434355830405 1988122516460518941718201)
    ·
      refine ⟨1491091887345389206288651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1988122516460518941718201 1491091887345389206288651)
      ·
        refine ⟨2236637831018083809432977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1491091887345389206288651 2236637831018083809432977)
        ·
          refine ⟨1677478373263562857074733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2236637831018083809432977 1677478373263562857074733)
          ·
            refine ⟨629054389973836071403025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1677478373263562857074733 629054389973836071403025)
            ·
              refine ⟨471790792480377053552269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 629054389973836071403025 471790792480377053552269)
              ·
                refine ⟨176921547180141395082101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 471790792480377053552269 176921547180141395082101)
                ·
                  refine ⟨16586395048138255788947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 176921547180141395082101 16586395048138255788947)
                  ·
                    rfl

theorem cell23_290717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_290717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290717 prefixEnd_290717 := by exact prefixLift 290717
  have htrace : WordTrace (prefixWord ++ tailWord_290717) baseStart_290717 baseEnd_290717 := by
    simpa [prefixWord, tailWord_290717, baseEnd_290717] using wordTrace_append hprefix tailTrace_290717
  have hstable : (prefixWord ++ tailWord_290717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290717).length < 2 ^ (prefixWord ++ tailWord_290717).sum := by decide
  have hdescent : baseEnd_290717 < baseStart_290717 := by decide
  rcases family_descends (prefixWord ++ tailWord_290717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290750 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_290750 : Nat := 118140960795 + 290750 * 2 ^ 59
def prefixEnd_290750 : Nat := 4983230072969 + 3 ^ 40 * 290750 * 2
def baseEnd_290750 : Nat := 149294500294842672987871

theorem tailTrace_290750 : CollatzResearch.WordTrace tailWord_290750 prefixEnd_290750 149294500294842672987871 := by
  unfold tailWord_290750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1325565462083735123972713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7069682464446587327854469 1325565462083735123972713)
  ·
    refine ⟨994174096562801342979535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1325565462083735123972713 994174096562801342979535)
    ·
      refine ⟨1491261144844202014469303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 994174096562801342979535 1491261144844202014469303)
      ·
        refine ⟨2236891717266303021703955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1491261144844202014469303 2236891717266303021703955)
        ·
          refine ⟨3355337575899454532555933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2236891717266303021703955 3355337575899454532555933)
          ·
            refine ⟨1258251590962295449708475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3355337575899454532555933 1258251590962295449708475)
            ·
              refine ⟨1887377386443443174562713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1258251590962295449708475 1887377386443443174562713)
              ·
                refine ⟨1415533039832582380922035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1887377386443443174562713 1415533039832582380922035)
                ·
                  refine ⟨2123299559748873571383053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1415533039832582380922035 2123299559748873571383053)
                  ·
                    refine ⟨796237334905827589268645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2123299559748873571383053 796237334905827589268645)
                    ·
                      refine ⟨149294500294842672987871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 796237334905827589268645 149294500294842672987871)
                      ·
                        rfl

theorem cell23_290750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_290750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290750 prefixEnd_290750 := by exact prefixLift 290750
  have htrace : WordTrace (prefixWord ++ tailWord_290750) baseStart_290750 baseEnd_290750 := by
    simpa [prefixWord, tailWord_290750, baseEnd_290750] using wordTrace_append hprefix tailTrace_290750
  have hstable : (prefixWord ++ tailWord_290750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290750).length < 2 ^ (prefixWord ++ tailWord_290750).sum := by decide
  have hdescent : baseEnd_290750 < baseStart_290750 := by decide
  rcases family_descends (prefixWord ++ tailWord_290750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290763 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 4]
def baseStart_290763 : Nat := 118140960795 + 290763 * 2 ^ 59
def prefixEnd_290763 : Nat := 4983230072969 + 3 ^ 40 * 290763 * 2
def baseEnd_290763 : Nat := 149301175543351122125311

theorem tailTrace_290763 : CollatzResearch.WordTrace tailWord_290763 prefixEnd_290763 149301175543351122125311 := by
  unfold tailWord_290763
  simp only [CollatzResearch.WordTrace]
  refine ⟨10604997845622784212004943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7069998563748522808003295 10604997845622784212004943)
  ·
    refine ⟨15907496768434176318007415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10604997845622784212004943 15907496768434176318007415)
    ·
      refine ⟨23861245152651264477011123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15907496768434176318007415 23861245152651264477011123)
      ·
        refine ⟨35791867728976896715516685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23861245152651264477011123 35791867728976896715516685)
        ·
          refine ⟨13421950398366336268318757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35791867728976896715516685 13421950398366336268318757)
          ·
            refine ⟨2516615699693688050309767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13421950398366336268318757 2516615699693688050309767)
            ·
              refine ⟨3774923549540532075464651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2516615699693688050309767 3774923549540532075464651)
              ·
                refine ⟨5662385324310798113196977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3774923549540532075464651 5662385324310798113196977)
                ·
                  refine ⟨4246788993233098584897733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5662385324310798113196977 4246788993233098584897733)
                  ·
                    refine ⟨796272936231205984668325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4246788993233098584897733 796272936231205984668325)
                    ·
                      refine ⟨149301175543351122125311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 796272936231205984668325 149301175543351122125311)
                      ·
                        rfl

theorem cell23_290763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 4].length) (baseStart_290763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290763 prefixEnd_290763 := by exact prefixLift 290763
  have htrace : WordTrace (prefixWord ++ tailWord_290763) baseStart_290763 baseEnd_290763 := by
    simpa [prefixWord, tailWord_290763, baseEnd_290763] using wordTrace_append hprefix tailTrace_290763
  have hstable : (prefixWord ++ tailWord_290763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290763).length < 2 ^ (prefixWord ++ tailWord_290763).sum := by decide
  have hdescent : baseEnd_290763 < baseStart_290763 := by decide
  rcases family_descends (prefixWord ++ tailWord_290763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290787 : List Nat := [1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 3]
def baseStart_290787 : Nat := 118140960795 + 290787 * 2 ^ 59
def prefixEnd_290787 : Nat := 4983230072969 + 3 ^ 40 * 290787 * 2
def baseEnd_290787 : Nat := 149313499079059028225201

theorem tailTrace_290787 : CollatzResearch.WordTrace tailWord_290787 prefixEnd_290787 149313499079059028225201 := by
  unfold tailWord_290787
  simp only [CollatzResearch.WordTrace]
  refine ⟨10605873197535836310878615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7070582131690557540585743 10605873197535836310878615)
  ·
    refine ⟨15908809796303754466317923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10605873197535836310878615 15908809796303754466317923)
    ·
      refine ⟨23863214694455631699476885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15908809796303754466317923 23863214694455631699476885)
      ·
        refine ⟨1118588188802607735912979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23863214694455631699476885 1118588188802607735912979)
        ·
          refine ⟨1677882283203911603869469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118588188802607735912979 1677882283203911603869469)
          ·
            refine ⟨629205856201466851451051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1677882283203911603869469 629205856201466851451051)
            ·
              refine ⟨943808784302200277176577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629205856201466851451051 943808784302200277176577)
              ·
                refine ⟨707856588226650207882433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 943808784302200277176577 707856588226650207882433)
                ·
                  refine ⟨530892441169987655911825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 707856588226650207882433 530892441169987655911825)
                  ·
                    refine ⟨398169330877490741933869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 530892441169987655911825 398169330877490741933869)
                    ·
                      refine ⟨149313499079059028225201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 398169330877490741933869 149313499079059028225201)
                      ·
                        rfl

theorem cell23_290787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_290787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290787 prefixEnd_290787 := by exact prefixLift 290787
  have htrace : WordTrace (prefixWord ++ tailWord_290787) baseStart_290787 baseEnd_290787 := by
    simpa [prefixWord, tailWord_290787, baseEnd_290787] using wordTrace_append hprefix tailTrace_290787
  have hstable : (prefixWord ++ tailWord_290787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290787).length < 2 ^ (prefixWord ++ tailWord_290787).sum := by decide
  have hdescent : baseEnd_290787 < baseStart_290787 := by decide
  rcases family_descends (prefixWord ++ tailWord_290787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290817 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_290817 : Nat := 118140960795 + 290817 * 2 ^ 59
def prefixEnd_290817 : Nat := 4983230072969 + 3 ^ 40 * 290817 * 2
def baseEnd_290817 : Nat := 149328903498693910850063

theorem tailTrace_290817 : CollatzResearch.WordTrace tailWord_290817 prefixEnd_290817 149328903498693910850063 := by
  unfold tailWord_290817
  simp only [CollatzResearch.WordTrace]
  refine ⟨10606967387427151434470705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7071311591618100956313803 10606967387427151434470705)
  ·
    refine ⟨7955225540570363575853029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10606967387427151434470705 7955225540570363575853029)
    ·
      refine ⟨1491604788856943170472443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7955225540570363575853029 1491604788856943170472443)
      ·
        refine ⟨2237407183285414755708665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1491604788856943170472443 2237407183285414755708665)
        ·
          refine ⟨1678055387464061066781499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2237407183285414755708665 1678055387464061066781499)
          ·
            refine ⟨2517083081196091600172249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1678055387464061066781499 2517083081196091600172249)
            ·
              refine ⟨1887812310897068700129187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2517083081196091600172249 1887812310897068700129187)
              ·
                refine ⟨2831718466345603050193781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1887812310897068700129187 2831718466345603050193781)
                ·
                  refine ⟨265473606219900285955667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2831718466345603050193781 265473606219900285955667)
                  ·
                    refine ⟨398210409329850428933501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 265473606219900285955667 398210409329850428933501)
                    ·
                      refine ⟨149328903498693910850063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 398210409329850428933501 149328903498693910850063)
                      ·
                        rfl

theorem cell23_290817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_290817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290817 prefixEnd_290817 := by exact prefixLift 290817
  have htrace : WordTrace (prefixWord ++ tailWord_290817) baseStart_290817 baseEnd_290817 := by
    simpa [prefixWord, tailWord_290817, baseEnd_290817] using wordTrace_append hprefix tailTrace_290817
  have hstable : (prefixWord ++ tailWord_290817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290817).length < 2 ^ (prefixWord ++ tailWord_290817).sum := by decide
  have hdescent : baseEnd_290817 < baseStart_290817 := by decide
  rcases family_descends (prefixWord ++ tailWord_290817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290844 : List Nat := [2, 2, 3, 1, 3, 1, 2, 2, 2, 3, 2]
def baseStart_290844 : Nat := 118140960795 + 290844 * 2 ^ 59
def prefixEnd_290844 : Nat := 4983230072969 + 3 ^ 40 * 290844 * 2
def baseEnd_290844 : Nat := 149342767476365305212439

theorem tailTrace_290844 : CollatzResearch.WordTrace tailWord_290844 prefixEnd_290844 149342767476365305212439 := by
  unfold tailWord_290844
  simp only [CollatzResearch.WordTrace]
  refine ⟨5303976079164667522851793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7071968105552890030469057 5303976079164667522851793)
  ·
    refine ⟨3977982059373500642138845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5303976079164667522851793 3977982059373500642138845)
    ·
      refine ⟨1491743272265062740802067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3977982059373500642138845 1491743272265062740802067)
      ·
        refine ⟨2237614908397594111203101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1491743272265062740802067 2237614908397594111203101)
        ·
          refine ⟨839105590649097791701163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2237614908397594111203101 839105590649097791701163)
          ·
            refine ⟨1258658385973646687551745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839105590649097791701163 1258658385973646687551745)
            ·
              refine ⟨943993789480235015663809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1258658385973646687551745 943993789480235015663809)
              ·
                refine ⟨707995342110176261747857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 943993789480235015663809 707995342110176261747857)
                ·
                  refine ⟨530996506582632196310893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 707995342110176261747857 530996506582632196310893)
                  ·
                    refine ⟨199123689968487073616585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 530996506582632196310893 199123689968487073616585)
                    ·
                      refine ⟨149342767476365305212439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 199123689968487073616585 149342767476365305212439)
                      ·
                        rfl

theorem cell23_290844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_290844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290844 prefixEnd_290844 := by exact prefixLift 290844
  have htrace : WordTrace (prefixWord ++ tailWord_290844) baseStart_290844 baseEnd_290844 := by
    simpa [prefixWord, tailWord_290844, baseEnd_290844] using wordTrace_append hprefix tailTrace_290844
  have hstable : (prefixWord ++ tailWord_290844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290844).length < 2 ^ (prefixWord ++ tailWord_290844).sum := by decide
  have hdescent : baseEnd_290844 < baseStart_290844 := by decide
  rcases family_descends (prefixWord ++ tailWord_290844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290850 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_290850 : Nat := 118140960795 + 290850 * 2 ^ 59
def prefixEnd_290850 : Nat := 4983230072969 + 3 ^ 40 * 290850 * 2
def baseEnd_290850 : Nat := 49781949453430760579137

theorem tailTrace_290850 : CollatzResearch.WordTrace tailWord_290850 prefixEnd_290850 49781949453430760579137 := by
  unfold tailWord_290850
  simp only [CollatzResearch.WordTrace]
  refine ⟨2652042749076899517605501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7072113997538398713614669 2652042749076899517605501)
  ·
    refine ⟨994516030903837319102063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2652042749076899517605501 994516030903837319102063)
    ·
      refine ⟨1491774046355755978653095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 994516030903837319102063 1491774046355755978653095)
      ·
        refine ⟨2237661069533633967979643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1491774046355755978653095 2237661069533633967979643)
        ·
          refine ⟨3356491604300450951969465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2237661069533633967979643 3356491604300450951969465)
          ·
            refine ⟨2517368703225338213977099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3356491604300450951969465 2517368703225338213977099)
            ·
              refine ⟨3776053054838007320965649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2517368703225338213977099 3776053054838007320965649)
              ·
                refine ⟨2832039791128505490724237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3776053054838007320965649 2832039791128505490724237)
                ·
                  refine ⟨1062014921673189559021589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2832039791128505490724237 1062014921673189559021589)
                  ·
                    refine ⟨49781949453430760579137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1062014921673189559021589 49781949453430760579137)
                    ·
                      rfl

theorem cell23_290850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_290850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290850 prefixEnd_290850 := by exact prefixLift 290850
  have htrace : WordTrace (prefixWord ++ tailWord_290850) baseStart_290850 baseEnd_290850 := by
    simpa [prefixWord, tailWord_290850, baseEnd_290850] using wordTrace_append hprefix tailTrace_290850
  have hstable : (prefixWord ++ tailWord_290850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290850).length < 2 ^ (prefixWord ++ tailWord_290850).sum := by decide
  have hdescent : baseEnd_290850 < baseStart_290850 := by decide
  rcases family_descends (prefixWord ++ tailWord_290850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290863 : List Nat := [1, 1, 2, 1, 2, 1, 1, 14]
def baseStart_290863 : Nat := 118140960795 + 290863 * 2 ^ 59
def prefixEnd_290863 : Nat := 4983230072969 + 3 ^ 40 * 290863 * 2
def baseEnd_290863 : Nat := 5531574948474101143513

theorem tailTrace_290863 : CollatzResearch.WordTrace tailWord_290863 prefixEnd_290863 5531574948474101143513 := by
  unfold tailWord_290863
  simp only [CollatzResearch.WordTrace]
  refine ⟨10608645145260501290645243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7072430096840334193763495 10608645145260501290645243)
  ·
    refine ⟨15912967717890751935967865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10608645145260501290645243 15912967717890751935967865)
    ·
      refine ⟨11934725788418063951975899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15912967717890751935967865 11934725788418063951975899)
      ·
        refine ⟨17902088682627095927963849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11934725788418063951975899 17902088682627095927963849)
        ·
          refine ⟨13426566511970321945972887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17902088682627095927963849 13426566511970321945972887)
          ·
            refine ⟨20139849767955482918959331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13426566511970321945972887 20139849767955482918959331)
            ·
              refine ⟨30209774651933224378438997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20139849767955482918959331 30209774651933224378438997)
              ·
                refine ⟨5531574948474101143513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 30209774651933224378438997 5531574948474101143513)
                ·
                  rfl

theorem cell23_290863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 14].length) (baseStart_290863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290863 prefixEnd_290863 := by exact prefixLift 290863
  have htrace : WordTrace (prefixWord ++ tailWord_290863) baseStart_290863 baseEnd_290863 := by
    simpa [prefixWord, tailWord_290863, baseEnd_290863] using wordTrace_append hprefix tailTrace_290863
  have hstable : (prefixWord ++ tailWord_290863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290863).length < 2 ^ (prefixWord ++ tailWord_290863).sum := by decide
  have hdescent : baseEnd_290863 < baseStart_290863 := by decide
  rcases family_descends (prefixWord ++ tailWord_290863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290867 : List Nat := [1, 1, 1, 2, 4, 1, 4, 3, 2, 4]
def baseStart_290867 : Nat := 118140960795 + 290867 * 2 ^ 59
def prefixEnd_290867 : Nat := 4983230072969 + 3 ^ 40 * 290867 * 2
def baseEnd_290867 : Nat := 49784859177139571741611

theorem tailTrace_290867 : CollatzResearch.WordTrace tailWord_290867 prefixEnd_290867 49784859177139571741611 := by
  unfold tailWord_290867
  simp only [CollatzResearch.WordTrace]
  refine ⟨10608791037246009973790855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7072527358164006649193903 10608791037246009973790855)
  ·
    refine ⟨15913186555869014960686283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10608791037246009973790855 15913186555869014960686283)
    ·
      refine ⟨23869779833803522441029425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15913186555869014960686283 23869779833803522441029425)
      ·
        refine ⟨17902334875352641830772069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23869779833803522441029425 17902334875352641830772069)
        ·
          refine ⟨3356687789128620343269763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17902334875352641830772069 3356687789128620343269763)
          ·
            refine ⟨5035031683692930514904645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3356687789128620343269763 5035031683692930514904645)
            ·
              refine ⟨944068440692424471544621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5035031683692930514904645 944068440692424471544621)
              ·
                refine ⟨354025665259659176829233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 944068440692424471544621 354025665259659176829233)
                ·
                  refine ⟨265519248944744382621925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 354025665259659176829233 265519248944744382621925)
                  ·
                    refine ⟨49784859177139571741611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 265519248944744382621925 49784859177139571741611)
                    ·
                      rfl

theorem cell23_290867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 4].length) (baseStart_290867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290867 prefixEnd_290867 := by exact prefixLift 290867
  have htrace : WordTrace (prefixWord ++ tailWord_290867) baseStart_290867 baseEnd_290867 := by
    simpa [prefixWord, tailWord_290867, baseEnd_290867] using wordTrace_append hprefix tailTrace_290867
  have hstable : (prefixWord ++ tailWord_290867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290867).length < 2 ^ (prefixWord ++ tailWord_290867).sum := by decide
  have hdescent : baseEnd_290867 < baseStart_290867 := by decide
  rcases family_descends (prefixWord ++ tailWord_290867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290877 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 3, 2, 3]
def baseStart_290877 : Nat := 118140960795 + 290877 * 2 ^ 59
def prefixEnd_290877 : Nat := 4983230072969 + 3 ^ 40 * 290877 * 2
def baseEnd_290877 : Nat := 149359712337963676099787

theorem tailTrace_290877 : CollatzResearch.WordTrace tailWord_290877 prefixEnd_290877 149359712337963676099787 := by
  unfold tailWord_290877
  simp only [CollatzResearch.WordTrace]
  refine ⟨10609155767209781681654885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7072770511473187787769923 10609155767209781681654885)
  ·
    refine ⟨1989216706351834065310291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10609155767209781681654885 1989216706351834065310291)
    ·
      refine ⟨2983825059527751097965437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1989216706351834065310291 2983825059527751097965437)
      ·
        refine ⟨1118934397322906661737039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2983825059527751097965437 1118934397322906661737039)
        ·
          refine ⟨1678401595984359992605559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118934397322906661737039 1678401595984359992605559)
          ·
            refine ⟨2517602393976539988908339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1678401595984359992605559 2517602393976539988908339)
            ·
              refine ⟨3776403590964809983362509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2517602393976539988908339 3776403590964809983362509)
              ·
                refine ⟨1416151346611803743760941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3776403590964809983362509 1416151346611803743760941)
                ·
                  refine ⟨531056754979426403910353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1416151346611803743760941 531056754979426403910353)
                  ·
                    refine ⟨398292566234569802932765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 531056754979426403910353 398292566234569802932765)
                    ·
                      refine ⟨149359712337963676099787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 398292566234569802932765 149359712337963676099787)
                      ·
                        rfl

theorem cell23_290877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_290877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290877 prefixEnd_290877 := by exact prefixLift 290877
  have htrace : WordTrace (prefixWord ++ tailWord_290877) baseStart_290877 baseEnd_290877 := by
    simpa [prefixWord, tailWord_290877, baseEnd_290877] using wordTrace_append hprefix tailTrace_290877
  have hstable : (prefixWord ++ tailWord_290877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290877).length < 2 ^ (prefixWord ++ tailWord_290877).sum := by decide
  have hdescent : baseEnd_290877 < baseStart_290877 := by decide
  rcases family_descends (prefixWord ++ tailWord_290877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290878 : List Nat := [4, 2, 1, 3, 2, 2, 1, 1, 2, 3, 2]
def baseStart_290878 : Nat := 118140960795 + 290878 * 2 ^ 59
def prefixEnd_290878 : Nat := 4983230072969 + 3 ^ 40 * 290878 * 2
def baseEnd_290878 : Nat := 149360225818618172187283

theorem tailTrace_290878 : CollatzResearch.WordTrace tailWord_290878 prefixEnd_290878 149360225818618172187283 := by
  unfold tailWord_290878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1326149030025769856555161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7072794826804105901627525 1326149030025769856555161)
  ·
    refine ⟨994611772519327392416371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1326149030025769856555161 994611772519327392416371)
    ·
      refine ⟨1491917658778991088624557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 994611772519327392416371 1491917658778991088624557)
      ·
        refine ⟨559469122042121658234209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1491917658778991088624557 559469122042121658234209)
        ·
          refine ⟨419601841531591243675657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 559469122042121658234209 419601841531591243675657)
          ·
            refine ⟨314701381148693432756743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 419601841531591243675657 314701381148693432756743)
            ·
              refine ⟨472052071723040149135115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314701381148693432756743 472052071723040149135115)
              ·
                refine ⟨708078107584560223702673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 472052071723040149135115 708078107584560223702673)
                ·
                  refine ⟨531058580688420167777005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 708078107584560223702673 531058580688420167777005)
                  ·
                    refine ⟨199146967758157562916377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 531058580688420167777005 199146967758157562916377)
                    ·
                      refine ⟨149360225818618172187283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 199146967758157562916377 149360225818618172187283)
                      ·
                        rfl

theorem cell23_290878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_290878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290878 prefixEnd_290878 := by exact prefixLift 290878
  have htrace : WordTrace (prefixWord ++ tailWord_290878) baseStart_290878 baseEnd_290878 := by
    simpa [prefixWord, tailWord_290878, baseEnd_290878] using wordTrace_append hprefix tailTrace_290878
  have hstable : (prefixWord ++ tailWord_290878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290878).length < 2 ^ (prefixWord ++ tailWord_290878).sum := by decide
  have hdescent : baseEnd_290878 < baseStart_290878 := by decide
  rcases family_descends (prefixWord ++ tailWord_290878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290894 : List Nat := [4, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3]
def baseStart_290894 : Nat := 118140960795 + 290894 * 2 ^ 59
def prefixEnd_290894 : Nat := 4983230072969 + 3 ^ 40 * 290894 * 2
def baseEnd_290894 : Nat := 149368441509090109587209

theorem tailTrace_290894 : CollatzResearch.WordTrace tailWord_290894 prefixEnd_290894 149368441509090109587209 := by
  unfold tailWord_290894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1326221976018524198127967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7073183872098795723349157 1326221976018524198127967)
  ·
    refine ⟨1989332964027786297191951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1326221976018524198127967 1989332964027786297191951)
    ·
      refine ⟨2983999446041679445787927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1989332964027786297191951 2983999446041679445787927)
      ·
        refine ⟨4475999169062519168681891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2983999446041679445787927 4475999169062519168681891)
        ·
          refine ⟨6713998753593778753022837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4475999169062519168681891 6713998753593778753022837)
          ·
            refine ⟨629437383149416758095891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6713998753593778753022837 629437383149416758095891)
            ·
              refine ⟨944156074724125137143837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629437383149416758095891 944156074724125137143837)
              ·
                refine ⟨354058528021546926428939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 944156074724125137143837 354058528021546926428939)
                ·
                  refine ⟨531087792032320389643409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 354058528021546926428939 531087792032320389643409)
                  ·
                    refine ⟨398315844024240292232557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 531087792032320389643409 398315844024240292232557)
                    ·
                      refine ⟨149368441509090109587209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 398315844024240292232557 149368441509090109587209)
                      ·
                        rfl

theorem cell23_290894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_290894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290894 prefixEnd_290894 := by exact prefixLift 290894
  have htrace : WordTrace (prefixWord ++ tailWord_290894) baseStart_290894 baseEnd_290894 := by
    simpa [prefixWord, tailWord_290894, baseEnd_290894] using wordTrace_append hprefix tailTrace_290894
  have hstable : (prefixWord ++ tailWord_290894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290894).length < 2 ^ (prefixWord ++ tailWord_290894).sum := by decide
  have hdescent : baseEnd_290894 < baseStart_290894 := by decide
  rcases family_descends (prefixWord ++ tailWord_290894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290900 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_290900 : Nat := 118140960795 + 290900 * 2 ^ 59
def prefixEnd_290900 : Nat := 4983230072969 + 3 ^ 40 * 290900 * 2
def baseEnd_290900 : Nat := 149371522393017086112181

theorem tailTrace_290900 : CollatzResearch.WordTrace tailWord_290900 prefixEnd_290900 149371522393017086112181 := by
  unfold tailWord_290900
  simp only [CollatzResearch.WordTrace]
  refine ⟨5304997323063228304871077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7073329764084304406494769 5304997323063228304871077)
  ·
    refine ⟨994686998074355307163327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5304997323063228304871077 994686998074355307163327)
    ·
      refine ⟨1492030497111532960744991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 994686998074355307163327 1492030497111532960744991)
      ·
        refine ⟨2238045745667299441117487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492030497111532960744991 2238045745667299441117487)
        ·
          refine ⟨3357068618500949161676231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2238045745667299441117487 3357068618500949161676231)
          ·
            refine ⟨5035602927751423742514347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3357068618500949161676231 5035602927751423742514347)
            ·
              refine ⟨7553404391627135613771521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5035602927751423742514347 7553404391627135613771521)
              ·
                refine ⟨5665053293720351710328641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7553404391627135613771521 5665053293720351710328641)
                ·
                  refine ⟨4248789970290263782746481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5665053293720351710328641 4248789970290263782746481)
                  ·
                    refine ⟨3186592477717697837059861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4248789970290263782746481 3186592477717697837059861)
                    ·
                      refine ⟨149371522393017086112181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3186592477717697837059861 149371522393017086112181)
                      ·
                        rfl

theorem cell23_290900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_290900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290900 prefixEnd_290900 := by exact prefixLift 290900
  have htrace : WordTrace (prefixWord ++ tailWord_290900) baseStart_290900 baseEnd_290900 := by
    simpa [prefixWord, tailWord_290900, baseEnd_290900] using wordTrace_append hprefix tailTrace_290900
  have hstable : (prefixWord ++ tailWord_290900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290900).length < 2 ^ (prefixWord ++ tailWord_290900).sum := by decide
  have hdescent : baseEnd_290900 < baseStart_290900 := by decide
  rcases family_descends (prefixWord ++ tailWord_290900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290908 : List Nat := [2, 2, 4, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_290908 : Nat := 118140960795 + 290908 * 2 ^ 59
def prefixEnd_290908 : Nat := 4983230072969 + 3 ^ 40 * 290908 * 2
def baseEnd_290908 : Nat := 149375630238253054812145

theorem tailTrace_290908 : CollatzResearch.WordTrace tailWord_290908 prefixEnd_290908 149375630238253054812145 := by
  unfold tailWord_290908
  simp only [CollatzResearch.WordTrace]
  refine ⟨5305143215048736988016689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7073524286731649317355585 5305143215048736988016689)
  ·
    refine ⟨3978857411286552741012517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5305143215048736988016689 3978857411286552741012517)
    ·
      refine ⟨746035764616228638939847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3978857411286552741012517 746035764616228638939847)
      ·
        refine ⟨1119053646924342958409771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 746035764616228638939847 1119053646924342958409771)
        ·
          refine ⟨1678580470386514437614657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1119053646924342958409771 1678580470386514437614657)
          ·
            refine ⟨1258935352789885828210993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1678580470386514437614657 1258935352789885828210993)
            ·
              refine ⟨944201514592414371158245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1258935352789885828210993 944201514592414371158245)
              ·
                refine ⟨177037783986077694592171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 944201514592414371158245 177037783986077694592171)
                ·
                  refine ⟨265556675979116541888257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177037783986077694592171 265556675979116541888257)
                  ·
                    refine ⟨199167506984337406416193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 265556675979116541888257 199167506984337406416193)
                    ·
                      refine ⟨149375630238253054812145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 199167506984337406416193 149375630238253054812145)
                      ·
                        rfl

theorem cell23_290908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_290908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290908 prefixEnd_290908 := by exact prefixLift 290908
  have htrace : WordTrace (prefixWord ++ tailWord_290908) baseStart_290908 baseEnd_290908 := by
    simpa [prefixWord, tailWord_290908, baseEnd_290908] using wordTrace_append hprefix tailTrace_290908
  have hstable : (prefixWord ++ tailWord_290908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290908).length < 2 ^ (prefixWord ++ tailWord_290908).sum := by decide
  have hdescent : baseEnd_290908 < baseStart_290908 := by decide
  rcases family_descends (prefixWord ++ tailWord_290908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290924 : List Nat := [2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 3]
def baseStart_290924 : Nat := 118140960795 + 290924 * 2 ^ 59
def prefixEnd_290924 : Nat := 4983230072969 + 3 ^ 40 * 290924 * 2
def baseEnd_290924 : Nat := 149383845928724992212071

theorem tailTrace_290924 : CollatzResearch.WordTrace tailWord_290924 prefixEnd_290924 149383845928724992212071 := by
  unfold tailWord_290924
  simp only [CollatzResearch.WordTrace]
  refine ⟨5305434999019754354307913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7073913332026339139077217 5305434999019754354307913)
  ·
    refine ⟨3979076249264815765730935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5305434999019754354307913 3979076249264815765730935)
    ·
      refine ⟨5968614373897223648596403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3979076249264815765730935 5968614373897223648596403)
      ·
        refine ⟨8952921560845835472894605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5968614373897223648596403 8952921560845835472894605)
        ·
          refine ⟨3357345585317188302335477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8952921560845835472894605 3357345585317188302335477)
          ·
            refine ⟨314751148623486403343951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3357345585317188302335477 314751148623486403343951)
            ·
              refine ⟨472126722935229605015927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314751148623486403343951 472126722935229605015927)
              ·
                refine ⟨708190084402844407523891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 472126722935229605015927 708190084402844407523891)
                ·
                  refine ⟨1062285126604266611285837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708190084402844407523891 1062285126604266611285837)
                  ·
                    refine ⟨398356922476599979232189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1062285126604266611285837 398356922476599979232189)
                    ·
                      refine ⟨149383845928724992212071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 398356922476599979232189 149383845928724992212071)
                      ·
                        rfl

theorem cell23_290924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 3].length) (baseStart_290924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290924 prefixEnd_290924 := by exact prefixLift 290924
  have htrace : WordTrace (prefixWord ++ tailWord_290924) baseStart_290924 baseEnd_290924 := by
    simpa [prefixWord, tailWord_290924, baseEnd_290924] using wordTrace_append hprefix tailTrace_290924
  have hstable : (prefixWord ++ tailWord_290924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290924).length < 2 ^ (prefixWord ++ tailWord_290924).sum := by decide
  have hdescent : baseEnd_290924 < baseStart_290924 := by decide
  rcases family_descends (prefixWord ++ tailWord_290924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290981 : List Nat := [1, 3, 1, 2, 1, 3, 3, 3, 2, 2, 2]
def baseStart_290981 : Nat := 118140960795 + 290981 * 2 ^ 59
def prefixEnd_290981 : Nat := 4983230072969 + 3 ^ 40 * 290981 * 2
def baseEnd_290981 : Nat := 149413114326031269199309

theorem tailTrace_290981 : CollatzResearch.WordTrace tailWord_290981 prefixEnd_290981 149413114326031269199309 := by
  unfold tailWord_290981
  simp only [CollatzResearch.WordTrace]
  refine ⟨10612948958833007443440797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7075299305888671628960531 10612948958833007443440797)
  ·
    refine ⟨3979855859562377791290299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10612948958833007443440797 3979855859562377791290299)
    ·
      refine ⟨5969783789343566686935449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3979855859562377791290299 5969783789343566686935449)
      ·
        refine ⟨4477337842007675015201587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5969783789343566686935449 4477337842007675015201587)
        ·
          refine ⟨6716006763011512522802381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4477337842007675015201587 6716006763011512522802381)
          ·
            refine ⟨2518502536129317196050893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6716006763011512522802381 2518502536129317196050893)
            ·
              refine ⟨944438451048493948519085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2518502536129317196050893 944438451048493948519085)
              ·
                refine ⟨354164419143185230694657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 944438451048493948519085 354164419143185230694657)
                ·
                  refine ⟨265623314357388923020993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 354164419143185230694657 265623314357388923020993)
                  ·
                    refine ⟨199217485768041692265745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 265623314357388923020993 199217485768041692265745)
                    ·
                      refine ⟨149413114326031269199309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 199217485768041692265745 149413114326031269199309)
                      ·
                        rfl

theorem cell23_290981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_290981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_290981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_290981 prefixEnd_290981 := by exact prefixLift 290981
  have htrace : WordTrace (prefixWord ++ tailWord_290981) baseStart_290981 baseEnd_290981 := by
    simpa [prefixWord, tailWord_290981, baseEnd_290981] using wordTrace_append hprefix tailTrace_290981
  have hstable : (prefixWord ++ tailWord_290981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290981).length < 2 ^ (prefixWord ++ tailWord_290981).sum := by decide
  have hdescent : baseEnd_290981 < baseStart_290981 := by decide
  rcases family_descends (prefixWord ++ tailWord_290981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291054 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 3, 6, 2]
def baseStart_291054 : Nat := 118140960795 + 291054 * 2 ^ 59
def prefixEnd_291054 : Nat := 4983230072969 + 3 ^ 40 * 291054 * 2
def baseEnd_291054 : Nat := 149450598413809483586473

theorem tailTrace_291054 : CollatzResearch.WordTrace tailWord_291054 prefixEnd_291054 149450598413809483586473 := by
  unfold tailWord_291054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1326951435946067613856027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7077074325045693940565477 1326951435946067613856027)
  ·
    refine ⟨1990427153919101420784041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1326951435946067613856027 1990427153919101420784041)
    ·
      refine ⟨1492820365439326065588031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1990427153919101420784041 1492820365439326065588031)
      ·
        refine ⟨2239230548158989098382047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492820365439326065588031 2239230548158989098382047)
        ·
          refine ⟨3358845822238483647573071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2239230548158989098382047 3358845822238483647573071)
          ·
            refine ⟨5038268733357725471359607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3358845822238483647573071 5038268733357725471359607)
            ·
              refine ⟨7557403100036588207039411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5038268733357725471359607 7557403100036588207039411)
              ·
                refine ⟨11336104650054882310559117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7557403100036588207039411 11336104650054882310559117)
                ·
                  refine ⟨4251039243770580866459669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11336104650054882310559117 4251039243770580866459669)
                  ·
                    refine ⟨199267464551745978115297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4251039243770580866459669 199267464551745978115297)
                    ·
                      refine ⟨149450598413809483586473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 199267464551745978115297 149450598413809483586473)
                      ·
                        rfl

theorem cell23_291054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_291054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291054 prefixEnd_291054 := by exact prefixLift 291054
  have htrace : WordTrace (prefixWord ++ tailWord_291054) baseStart_291054 baseEnd_291054 := by
    simpa [prefixWord, tailWord_291054, baseEnd_291054] using wordTrace_append hprefix tailTrace_291054
  have hstable : (prefixWord ++ tailWord_291054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291054).length < 2 ^ (prefixWord ++ tailWord_291054).sum := by decide
  have hdescent : baseEnd_291054 < baseStart_291054 := by decide
  rcases family_descends (prefixWord ++ tailWord_291054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291077 : List Nat := [1, 3, 1, 1, 2, 1, 2, 6, 6]
def baseStart_291077 : Nat := 118140960795 + 291077 * 2 ^ 59
def prefixEnd_291077 : Nat := 4983230072969 + 3 ^ 40 * 291077 * 2
def baseEnd_291077 : Nat := 16606934274318099288763

theorem tailTrace_291077 : CollatzResearch.WordTrace tailWord_291077 prefixEnd_291077 16606934274318099288763 := by
  unfold tailWord_291077
  simp only [CollatzResearch.WordTrace]
  refine ⟨10616450366485215838935485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7077633577656810559290323 10616450366485215838935485)
  ·
    refine ⟨3981168887431955939600807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10616450366485215838935485 3981168887431955939600807)
    ·
      refine ⟨5971753331147933909401211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3981168887431955939600807 5971753331147933909401211)
      ·
        refine ⟨8957629996721900864101817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5971753331147933909401211 8957629996721900864101817)
        ·
          refine ⟨6718222497541425648076363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8957629996721900864101817 6718222497541425648076363)
          ·
            refine ⟨10077333746312138472114545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6718222497541425648076363 10077333746312138472114545)
            ·
              refine ⟨7558000309734103854085909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10077333746312138472114545 7558000309734103854085909)
              ·
                refine ⟨354281264518786118160277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7558000309734103854085909 354281264518786118160277)
                ·
                  refine ⟨16606934274318099288763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 354281264518786118160277 16606934274318099288763)
                  ·
                    rfl

theorem cell23_291077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 6].length) (baseStart_291077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291077 prefixEnd_291077 := by exact prefixLift 291077
  have htrace : WordTrace (prefixWord ++ tailWord_291077) baseStart_291077 baseEnd_291077 := by
    simpa [prefixWord, tailWord_291077, baseEnd_291077] using wordTrace_append hprefix tailTrace_291077
  have hstable : (prefixWord ++ tailWord_291077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291077).length < 2 ^ (prefixWord ++ tailWord_291077).sum := by decide
  have hdescent : baseEnd_291077 < baseStart_291077 := by decide
  rcases family_descends (prefixWord ++ tailWord_291077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291081 : List Nat := [1, 2, 1, 1, 3, 4, 2, 4, 1, 4]
def baseStart_291081 : Nat := 118140960795 + 291081 * 2 ^ 59
def prefixEnd_291081 : Nat := 4983230072969 + 3 ^ 40 * 291081 * 2
def baseEnd_291081 : Nat := 49821487463826959316283

theorem tailTrace_291081 : CollatzResearch.WordTrace tailWord_291081 prefixEnd_291081 49821487463826959316283 := by
  unfold tailWord_291081
  simp only [CollatzResearch.WordTrace]
  refine ⟨10616596258470724522081097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7077730838980483014720731 10616596258470724522081097)
  ·
    refine ⟨7962447193853043391560823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10616596258470724522081097 7962447193853043391560823)
    ·
      refine ⟨11943670790779565087341235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7962447193853043391560823 11943670790779565087341235)
      ·
        refine ⟨17915506186169347631011853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11943670790779565087341235 17915506186169347631011853)
        ·
          refine ⟨6718314819813505361629445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17915506186169347631011853 6718314819813505361629445)
          ·
            refine ⟨1259684028715032255305521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6718314819813505361629445 1259684028715032255305521)
            ·
              refine ⟨944763021536274191479141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1259684028715032255305521 944763021536274191479141)
              ·
                refine ⟨177143066538051410902339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 944763021536274191479141 177143066538051410902339)
                ·
                  refine ⟨265714599807077116353509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177143066538051410902339 265714599807077116353509)
                  ·
                    refine ⟨49821487463826959316283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 265714599807077116353509 49821487463826959316283)
                    ·
                      rfl

theorem cell23_291081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 1, 4].length) (baseStart_291081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291081 prefixEnd_291081 := by exact prefixLift 291081
  have htrace : WordTrace (prefixWord ++ tailWord_291081) baseStart_291081 baseEnd_291081 := by
    simpa [prefixWord, tailWord_291081, baseEnd_291081] using wordTrace_append hprefix tailTrace_291081
  have hstable : (prefixWord ++ tailWord_291081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291081).length < 2 ^ (prefixWord ++ tailWord_291081).sum := by decide
  have hdescent : baseEnd_291081 < baseStart_291081 := by decide
  rcases family_descends (prefixWord ++ tailWord_291081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291147 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 5]
def baseStart_291147 : Nat := 118140960795 + 291147 * 2 ^ 59
def prefixEnd_291147 : Nat := 4983230072969 + 3 ^ 40 * 291147 * 2
def baseEnd_291147 : Nat := 149498352114677619723545

theorem tailTrace_291147 : CollatzResearch.WordTrace tailWord_291147 prefixEnd_291147 149498352114677619723545 := by
  unfold tailWord_291147
  simp only [CollatzResearch.WordTrace]
  refine ⟨10619003476231617793983695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7079335650821078529322463 10619003476231617793983695)
  ·
    refine ⟨15928505214347426690975543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10619003476231617793983695 15928505214347426690975543)
    ·
      refine ⟨23892757821521140036463315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15928505214347426690975543 23892757821521140036463315)
      ·
        refine ⟨35839136732281710054694973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23892757821521140036463315 35839136732281710054694973)
        ·
          refine ⟨13439676274605641270510615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35839136732281710054694973 13439676274605641270510615)
          ·
            refine ⟨20159514411908461905765923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13439676274605641270510615 20159514411908461905765923)
            ·
              refine ⟨30239271617862692858648885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20159514411908461905765923 30239271617862692858648885)
              ·
                refine ⟨2834931714174627455498333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30239271617862692858648885 2834931714174627455498333)
                ·
                  refine ⟨1063099392815485295811875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2834931714174627455498333 1063099392815485295811875)
                  ·
                    refine ⟨1594649089223227943717813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1063099392815485295811875 1594649089223227943717813)
                    ·
                      refine ⟨149498352114677619723545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1594649089223227943717813 149498352114677619723545)
                      ·
                        rfl

theorem cell23_291147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 5].length) (baseStart_291147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291147 prefixEnd_291147 := by exact prefixLift 291147
  have htrace : WordTrace (prefixWord ++ tailWord_291147) baseStart_291147 baseEnd_291147 := by
    simpa [prefixWord, tailWord_291147, baseEnd_291147] using wordTrace_append hprefix tailTrace_291147
  have hstable : (prefixWord ++ tailWord_291147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291147).length < 2 ^ (prefixWord ++ tailWord_291147).sum := by decide
  have hdescent : baseEnd_291147 < baseStart_291147 := by decide
  rcases family_descends (prefixWord ++ tailWord_291147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291161 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 5, 2, 2]
def baseStart_291161 : Nat := 118140960795 + 291161 * 2 ^ 59
def prefixEnd_291161 : Nat := 4983230072969 + 3 ^ 40 * 291161 * 2
def baseEnd_291161 : Nat := 149505540843840564948481

theorem tailTrace_291161 : CollatzResearch.WordTrace tailWord_291161 prefixEnd_291161 149505540843840564948481 := by
  unfold tailWord_291161
  simp only [CollatzResearch.WordTrace]
  refine ⟨10619514098180898184993337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7079676065453932123328891 10619514098180898184993337)
  ·
    refine ⟨7964635573635673638745003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10619514098180898184993337 7964635573635673638745003)
    ·
      refine ⟨11946953360453510458117505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7964635573635673638745003 11946953360453510458117505)
      ·
        refine ⟨8960215020340132843588129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11946953360453510458117505 8960215020340132843588129)
        ·
          refine ⟨6720161265255099632691097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8960215020340132843588129 6720161265255099632691097)
          ·
            refine ⟨5040120948941324724518323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6720161265255099632691097 5040120948941324724518323)
            ·
              refine ⟨7560181423411987086777485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5040120948941324724518323 7560181423411987086777485)
              ·
                refine ⟨2835068033779495157541557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7560181423411987086777485 2835068033779495157541557)
                ·
                  refine ⟨265787628166827671019521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2835068033779495157541557 265787628166827671019521)
                  ·
                    refine ⟨199340721125120753264641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 265787628166827671019521 199340721125120753264641)
                    ·
                      refine ⟨149505540843840564948481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 199340721125120753264641 149505540843840564948481)
                      ·
                        rfl

theorem cell23_291161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 2, 2].length) (baseStart_291161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291161 prefixEnd_291161 := by exact prefixLift 291161
  have htrace : WordTrace (prefixWord ++ tailWord_291161) baseStart_291161 baseEnd_291161 := by
    simpa [prefixWord, tailWord_291161, baseEnd_291161] using wordTrace_append hprefix tailTrace_291161
  have hstable : (prefixWord ++ tailWord_291161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291161).length < 2 ^ (prefixWord ++ tailWord_291161).sum := by decide
  have hdescent : baseEnd_291161 < baseStart_291161 := by decide
  rcases family_descends (prefixWord ++ tailWord_291161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291167 : List Nat := [1, 1, 2, 3, 1, 2, 4, 9]
def baseStart_291167 : Nat := 118140960795 + 291167 * 2 ^ 59
def prefixEnd_291167 : Nat := 4983230072969 + 3 ^ 40 * 291167 * 2
def baseEnd_291167 : Nat := 5537356360287686721239

theorem tailTrace_291167 : CollatzResearch.WordTrace tailWord_291167 prefixEnd_291167 5537356360287686721239 := by
  unfold tailWord_291167
  simp only [CollatzResearch.WordTrace]
  refine ⟨10619732936159161209711755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7079821957439440806474503 10619732936159161209711755)
  ·
    refine ⟨15929599404238741814567633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10619732936159161209711755 15929599404238741814567633)
    ·
      refine ⟨11947199553179056360925725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15929599404238741814567633 11947199553179056360925725)
      ·
        refine ⟨4480199832442146135347147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11947199553179056360925725 4480199832442146135347147)
        ·
          refine ⟨6720299748663219203020721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4480199832442146135347147 6720299748663219203020721)
          ·
            refine ⟨5040224811497414402265541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6720299748663219203020721 5040224811497414402265541)
            ·
              refine ⟨945042152155765200424789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5040224811497414402265541 945042152155765200424789)
              ·
                refine ⟨5537356360287686721239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 945042152155765200424789 5537356360287686721239)
                ·
                  rfl

theorem cell23_291167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 9].length) (baseStart_291167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291167 prefixEnd_291167 := by exact prefixLift 291167
  have htrace : WordTrace (prefixWord ++ tailWord_291167) baseStart_291167 baseEnd_291167 := by
    simpa [prefixWord, tailWord_291167, baseEnd_291167] using wordTrace_append hprefix tailTrace_291167
  have hstable : (prefixWord ++ tailWord_291167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291167).length < 2 ^ (prefixWord ++ tailWord_291167).sum := by decide
  have hdescent : baseEnd_291167 < baseStart_291167 := by decide
  rcases family_descends (prefixWord ++ tailWord_291167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291195 : List Nat := [1, 1, 1, 1, 1, 8, 1, 4, 1, 2, 2]
def baseStart_291195 : Nat := 118140960795 + 291195 * 2 ^ 59
def prefixEnd_291195 : Nat := 4983230072969 + 3 ^ 40 * 291195 * 2
def baseEnd_291195 : Nat := 149522999186093431923325

theorem tailTrace_291195 : CollatzResearch.WordTrace tailWord_291195 prefixEnd_291195 149522999186093431923325 := by
  unfold tailWord_291195
  simp only [CollatzResearch.WordTrace]
  refine ⟨10620754180057721991731039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7080502786705147994487359 10620754180057721991731039)
  ·
    refine ⟨15931131270086582987596559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10620754180057721991731039 15931131270086582987596559)
    ·
      refine ⟨23896696905129874481394839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15931131270086582987596559 23896696905129874481394839)
      ·
        refine ⟨35845045357694811722092259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23896696905129874481394839 35845045357694811722092259)
        ·
          refine ⟨53767568036542217583138389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35845045357694811722092259 53767568036542217583138389)
          ·
            refine ⟨630088687928229112302403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 53767568036542217583138389 630088687928229112302403)
            ·
              refine ⟨945133031892343668453605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630088687928229112302403 945133031892343668453605)
              ·
                refine ⟨177212443479814437835051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 945133031892343668453605 177212443479814437835051)
                ·
                  refine ⟨265818665219721656752577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177212443479814437835051 265818665219721656752577)
                  ·
                    refine ⟨199363998914791242564433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 265818665219721656752577 199363998914791242564433)
                    ·
                      refine ⟨149522999186093431923325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 199363998914791242564433 149522999186093431923325)
                      ·
                        rfl

theorem cell23_291195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 1, 2, 2].length) (baseStart_291195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291195 prefixEnd_291195 := by exact prefixLift 291195
  have htrace : WordTrace (prefixWord ++ tailWord_291195) baseStart_291195 baseEnd_291195 := by
    simpa [prefixWord, tailWord_291195, baseEnd_291195] using wordTrace_append hprefix tailTrace_291195
  have hstable : (prefixWord ++ tailWord_291195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291195).length < 2 ^ (prefixWord ++ tailWord_291195).sum := by decide
  have hdescent : baseEnd_291195 < baseStart_291195 := by decide
  rcases family_descends (prefixWord ++ tailWord_291195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291201 : List Nat := [1, 2, 4, 3, 1, 3, 1, 8]
def baseStart_291201 : Nat := 118140960795 + 291201 * 2 ^ 59
def prefixEnd_291201 : Nat := 4983230072969 + 3 ^ 40 * 291201 * 2
def baseEnd_291201 : Nat := 5538002965556311424011

theorem tailTrace_291201 : CollatzResearch.WordTrace tailWord_291201 prefixEnd_291201 5538002965556311424011 := by
  unfold tailWord_291201
  simp only [CollatzResearch.WordTrace]
  refine ⟨10620973018035985016449457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7080648678690656677632971 10620973018035985016449457)
  ·
    refine ⟨7965729763526988762337093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10620973018035985016449457 7965729763526988762337093)
    ·
      refine ⟨1493574330661310392938205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7965729763526988762337093 1493574330661310392938205)
      ·
        refine ⟨560090373997991397351827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1493574330661310392938205 560090373997991397351827)
        ·
          refine ⟨840135560996987096027741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560090373997991397351827 840135560996987096027741)
          ·
            refine ⟨315050835373870161010403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 840135560996987096027741 315050835373870161010403)
            ·
              refine ⟨472576253060805241515605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315050835373870161010403 472576253060805241515605)
              ·
                refine ⟨5538002965556311424011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 472576253060805241515605 5538002965556311424011)
                ·
                  rfl

theorem cell23_291201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 8].length) (baseStart_291201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291201 prefixEnd_291201 := by exact prefixLift 291201
  have htrace : WordTrace (prefixWord ++ tailWord_291201) baseStart_291201 baseEnd_291201 := by
    simpa [prefixWord, tailWord_291201, baseEnd_291201] using wordTrace_append hprefix tailTrace_291201
  have hstable : (prefixWord ++ tailWord_291201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291201).length < 2 ^ (prefixWord ++ tailWord_291201).sum := by decide
  have hdescent : baseEnd_291201 < baseStart_291201 := by decide
  rcases family_descends (prefixWord ++ tailWord_291201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291211 : List Nat := [1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 3]
def baseStart_291211 : Nat := 118140960795 + 291211 * 2 ^ 59
def prefixEnd_291211 : Nat := 4983230072969 + 3 ^ 40 * 291211 * 2
def baseEnd_291211 : Nat := 149531214876565369323251

theorem tailTrace_291211 : CollatzResearch.WordTrace tailWord_291211 prefixEnd_291211 149531214876565369323251 := by
  unfold tailWord_291211
  simp only [CollatzResearch.WordTrace]
  refine ⟨10621337747999756724313487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7080891831999837816208991 10621337747999756724313487)
  ·
    refine ⟨15932006621999635086470231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10621337747999756724313487 15932006621999635086470231)
    ·
      refine ⟨23898009932999452629705347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15932006621999635086470231 23898009932999452629705347)
      ·
        refine ⟨35847014899499178944558021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23898009932999452629705347 35847014899499178944558021)
        ·
          refine ⟨6721315293656096052104629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35847014899499178944558021 6721315293656096052104629)
          ·
            refine ⟨630123308780259004884809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6721315293656096052104629 630123308780259004884809)
            ·
              refine ⟨472592481585194253663607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 630123308780259004884809 472592481585194253663607)
              ·
                refine ⟨708888722377791380495411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 472592481585194253663607 708888722377791380495411)
                ·
                  refine ⟨1063333083566687070743117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708888722377791380495411 1063333083566687070743117)
                  ·
                    refine ⟨398749906337507651528669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1063333083566687070743117 398749906337507651528669)
                    ·
                      refine ⟨149531214876565369323251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 398749906337507651528669 149531214876565369323251)
                      ·
                        rfl

theorem cell23_291211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 3].length) (baseStart_291211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291211 prefixEnd_291211 := by exact prefixLift 291211
  have htrace : WordTrace (prefixWord ++ tailWord_291211) baseStart_291211 baseEnd_291211 := by
    simpa [prefixWord, tailWord_291211, baseEnd_291211] using wordTrace_append hprefix tailTrace_291211
  have hstable : (prefixWord ++ tailWord_291211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291211).length < 2 ^ (prefixWord ++ tailWord_291211).sum := by decide
  have hdescent : baseEnd_291211 < baseStart_291211 := by decide
  rcases family_descends (prefixWord ++ tailWord_291211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291217 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 10]
def baseStart_291217 : Nat := 118140960795 + 291217 * 2 ^ 59
def prefixEnd_291217 : Nat := 4983230072969 + 3 ^ 40 * 291217 * 2
def baseEnd_291217 : Nat := 149534295760492345848223

theorem tailTrace_291217 : CollatzResearch.WordTrace tailWord_291217 prefixEnd_291217 149534295760492345848223 := by
  unfold tailWord_291217
  simp only [CollatzResearch.WordTrace]
  refine ⟨10621556585978019749031905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7081037723985346499354603 10621556585978019749031905)
  ·
    refine ⟨7966167439483514811773929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10621556585978019749031905 7966167439483514811773929)
    ·
      refine ⟨5974625579612636108830447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7966167439483514811773929 5974625579612636108830447)
      ·
        refine ⟨8961938369418954163245671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5974625579612636108830447 8961938369418954163245671)
        ·
          refine ⟨13442907554128431244868507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8961938369418954163245671 13442907554128431244868507)
          ·
            refine ⟨20164361331192646867302761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13442907554128431244868507 20164361331192646867302761)
            ·
              refine ⟨15123270998394485150477071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20164361331192646867302761 15123270998394485150477071)
              ·
                refine ⟨22684906497591727725715607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15123270998394485150477071 22684906497591727725715607)
                ·
                  refine ⟨34027359746387591588573411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22684906497591727725715607 34027359746387591588573411)
                  ·
                    refine ⟨51041039619581387382860117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34027359746387591588573411 51041039619581387382860117)
                    ·
                      refine ⟨149534295760492345848223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 51041039619581387382860117 149534295760492345848223)
                      ·
                        rfl

theorem cell23_291217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_291217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291217 prefixEnd_291217 := by exact prefixLift 291217
  have htrace : WordTrace (prefixWord ++ tailWord_291217) baseStart_291217 baseEnd_291217 := by
    simpa [prefixWord, tailWord_291217, baseEnd_291217] using wordTrace_append hprefix tailTrace_291217
  have hstable : (prefixWord ++ tailWord_291217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291217).length < 2 ^ (prefixWord ++ tailWord_291217).sum := by decide
  have hdescent : baseEnd_291217 < baseStart_291217 := by decide
  rcases family_descends (prefixWord ++ tailWord_291217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291245 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_291245 : Nat := 118140960795 + 291245 * 2 ^ 59
def prefixEnd_291245 : Nat := 4983230072969 + 3 ^ 40 * 291245 * 2
def baseEnd_291245 : Nat := 149548673218818236298095

theorem tailTrace_291245 : CollatzResearch.WordTrace tailWord_291245 prefixEnd_291245 149548673218818236298095 := by
  unfold tailWord_291245
  simp only [CollatzResearch.WordTrace]
  refine ⟨10622577829876580531051189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7081718553251053687367459 10622577829876580531051189)
  ·
    refine ⟨995866671550929424786049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10622577829876580531051189 995866671550929424786049)
    ·
      refine ⟨746900003663197068589537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 995866671550929424786049 746900003663197068589537)
      ·
        refine ⟨560175002747397801442153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 746900003663197068589537 560175002747397801442153)
        ·
          refine ⟨420131252060548351081615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 560175002747397801442153 420131252060548351081615)
          ·
            refine ⟨630196878090822526622423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420131252060548351081615 630196878090822526622423)
            ·
              refine ⟨945295317136233789933635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630196878090822526622423 945295317136233789933635)
              ·
                refine ⟨1417942975704350684900453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945295317136233789933635 1417942975704350684900453)
                ·
                  refine ⟨265864307944565753418835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1417942975704350684900453 265864307944565753418835)
                  ·
                    refine ⟨398796461916848630128253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 265864307944565753418835 398796461916848630128253)
                    ·
                      refine ⟨149548673218818236298095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 398796461916848630128253 149548673218818236298095)
                      ·
                        rfl

theorem cell23_291245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_291245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291245 prefixEnd_291245 := by exact prefixLift 291245
  have htrace : WordTrace (prefixWord ++ tailWord_291245) baseStart_291245 baseEnd_291245 := by
    simpa [prefixWord, tailWord_291245, baseEnd_291245] using wordTrace_append hprefix tailTrace_291245
  have hstable : (prefixWord ++ tailWord_291245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291245).length < 2 ^ (prefixWord ++ tailWord_291245).sum := by decide
  have hdescent : baseEnd_291245 < baseStart_291245 := by decide
  rcases family_descends (prefixWord ++ tailWord_291245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291274 : List Nat := [3, 1, 2, 1, 2, 2, 1, 4, 7]
def baseStart_291274 : Nat := 118140960795 + 291274 * 2 ^ 59
def prefixEnd_291274 : Nat := 4983230072969 + 3 ^ 40 * 291274 * 2
def baseEnd_291274 : Nat := 16618173795310958092829

theorem tailTrace_291274 : CollatzResearch.WordTrace tailWord_291274 prefixEnd_291274 16618173795310958092829 := by
  unfold tailWord_291274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2655908886692879620964219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7082423697847678989237917 2655908886692879620964219)
  ·
    refine ⟨3983863330039319431446329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2655908886692879620964219 3983863330039319431446329)
    ·
      refine ⟨2987897497529489573584747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3983863330039319431446329 2987897497529489573584747)
      ·
        refine ⟨4481846246294234360377121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2987897497529489573584747 4481846246294234360377121)
        ·
          refine ⟨3361384684720675770282841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4481846246294234360377121 3361384684720675770282841)
          ·
            refine ⟨2521038513540506827712131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3361384684720675770282841 2521038513540506827712131)
            ·
              refine ⟨3781557770310760241568197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2521038513540506827712131 3781557770310760241568197)
              ·
                refine ⟨709042081933267545294037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3781557770310760241568197 709042081933267545294037)
                ·
                  refine ⟨16618173795310958092829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 709042081933267545294037 16618173795310958092829)
                  ·
                    rfl

theorem cell23_291274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 7].length) (baseStart_291274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291274 prefixEnd_291274 := by exact prefixLift 291274
  have htrace : WordTrace (prefixWord ++ tailWord_291274) baseStart_291274 baseEnd_291274 := by
    simpa [prefixWord, tailWord_291274, baseEnd_291274] using wordTrace_append hprefix tailTrace_291274
  have hstable : (prefixWord ++ tailWord_291274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291274).length < 2 ^ (prefixWord ++ tailWord_291274).sum := by decide
  have hdescent : baseEnd_291274 < baseStart_291274 := by decide
  rcases family_descends (prefixWord ++ tailWord_291274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291308 : List Nat := [2, 2, 1, 1, 2, 1, 7, 2, 5]
def baseStart_291308 : Nat := 118140960795 + 291308 * 2 ^ 59
def prefixEnd_291308 : Nat := 4983230072969 + 3 ^ 40 * 291308 * 2
def baseEnd_291308 : Nat := 16620113611116832201145

theorem tailTrace_291308 : CollatzResearch.WordTrace tailWord_291308 prefixEnd_291308 16620113611116832201145 := by
  unfold tailWord_291308
  simp only [CollatzResearch.WordTrace]
  refine ⟨5312437814324171145297289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7083250419098894860396385 5312437814324171145297289)
  ·
    refine ⟨3984328360743128358972967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5312437814324171145297289 3984328360743128358972967)
    ·
      refine ⟨5976492541114692538459451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3984328360743128358972967 5976492541114692538459451)
      ·
        refine ⟨8964738811672038807689177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5976492541114692538459451 8964738811672038807689177)
        ·
          refine ⟨6723554108754029105766883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8964738811672038807689177 6723554108754029105766883)
          ·
            refine ⟨10085331163131043658650325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6723554108754029105766883 10085331163131043658650325)
            ·
              refine ⟨236374949135883835749617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10085331163131043658650325 236374949135883835749617)
              ·
                refine ⟨177281211851912876812213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236374949135883835749617 177281211851912876812213)
                ·
                  refine ⟨16620113611116832201145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 177281211851912876812213 16620113611116832201145)
                  ·
                    rfl

theorem cell23_291308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 5].length) (baseStart_291308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291308 prefixEnd_291308 := by exact prefixLift 291308
  have htrace : WordTrace (prefixWord ++ tailWord_291308) baseStart_291308 baseEnd_291308 := by
    simpa [prefixWord, tailWord_291308, baseEnd_291308] using wordTrace_append hprefix tailTrace_291308
  have hstable : (prefixWord ++ tailWord_291308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291308).length < 2 ^ (prefixWord ++ tailWord_291308).sum := by decide
  have hdescent : baseEnd_291308 < baseStart_291308 := by decide
  rcases family_descends (prefixWord ++ tailWord_291308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291311 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 2, 5, 2]
def baseStart_291311 : Nat := 118140960795 + 291311 * 2 ^ 59
def prefixEnd_291311 : Nat := 4983230072969 + 3 ^ 40 * 291311 * 2
def baseEnd_291311 : Nat := 149582562942014978072791

theorem tailTrace_291311 : CollatzResearch.WordTrace tailWord_291311 prefixEnd_291311 149582562942014978072791 := by
  unfold tailWord_291311
  simp only [CollatzResearch.WordTrace]
  refine ⟨10624985047637473802953787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7083323365091649201969191 10624985047637473802953787)
  ·
    refine ⟨15937477571456210704430681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10624985047637473802953787 15937477571456210704430681)
    ·
      refine ⟨11953108178592158028323011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15937477571456210704430681 11953108178592158028323011)
      ·
        refine ⟨17929662267888237042484517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11953108178592158028323011 17929662267888237042484517)
        ·
          refine ⟨3361811675229044445465847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17929662267888237042484517 3361811675229044445465847)
          ·
            refine ⟨5042717512843566668198771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3361811675229044445465847 5042717512843566668198771)
            ·
              refine ⟨7564076269265350002298157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5042717512843566668198771 7564076269265350002298157)
              ·
                refine ⟨2836528600974506250861809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7564076269265350002298157 2836528600974506250861809)
                ·
                  refine ⟨2127396450730879688146357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2836528600974506250861809 2127396450730879688146357)
                  ·
                    refine ⟨199443417256019970763721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2127396450730879688146357 199443417256019970763721)
                    ·
                      refine ⟨149582562942014978072791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 199443417256019970763721 149582562942014978072791)
                      ·
                        rfl

theorem cell23_291311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 5, 2].length) (baseStart_291311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291311 prefixEnd_291311 := by exact prefixLift 291311
  have htrace : WordTrace (prefixWord ++ tailWord_291311) baseStart_291311 baseEnd_291311 := by
    simpa [prefixWord, tailWord_291311, baseEnd_291311] using wordTrace_append hprefix tailTrace_291311
  have hstable : (prefixWord ++ tailWord_291311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291311).length < 2 ^ (prefixWord ++ tailWord_291311).sum := by decide
  have hdescent : baseEnd_291311 < baseStart_291311 := by decide
  rcases family_descends (prefixWord ++ tailWord_291311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291348 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_291348 : Nat := 118140960795 + 291348 * 2 ^ 59
def prefixEnd_291348 : Nat := 4983230072969 + 3 ^ 40 * 291348 * 2
def baseEnd_291348 : Nat := 149601561726231333310121

theorem tailTrace_291348 : CollatzResearch.WordTrace tailWord_291348 prefixEnd_291348 149601561726231333310121 := by
  unfold tailWord_291348
  simp only [CollatzResearch.WordTrace]
  refine ⟨5313167274251714561025349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7084223032335619414700465 5313167274251714561025349)
  ·
    refine ⟨996218863922196480192253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5313167274251714561025349 996218863922196480192253)
    ·
      refine ⟨373582073970823680072095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 996218863922196480192253 373582073970823680072095)
      ·
        refine ⟨560373110956235520108143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373582073970823680072095 560373110956235520108143)
        ·
          refine ⟨840559666434353280162215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560373110956235520108143 840559666434353280162215)
          ·
            refine ⟨1260839499651529920243323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840559666434353280162215 1260839499651529920243323)
            ·
              refine ⟨1891259249477294880364985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260839499651529920243323 1891259249477294880364985)
              ·
                refine ⟨1418444437107971160273739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1891259249477294880364985 1418444437107971160273739)
                ·
                  refine ⟨2127666655661956740410609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418444437107971160273739 2127666655661956740410609)
                  ·
                    refine ⟨1595749991746467555307957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2127666655661956740410609 1595749991746467555307957)
                    ·
                      refine ⟨149601561726231333310121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1595749991746467555307957 149601561726231333310121)
                      ·
                        rfl

theorem cell23_291348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_291348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291348 prefixEnd_291348 := by exact prefixLift 291348
  have htrace : WordTrace (prefixWord ++ tailWord_291348) baseStart_291348 baseEnd_291348 := by
    simpa [prefixWord, tailWord_291348, baseEnd_291348] using wordTrace_append hprefix tailTrace_291348
  have hstable : (prefixWord ++ tailWord_291348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291348).length < 2 ^ (prefixWord ++ tailWord_291348).sum := by decide
  have hdescent : baseEnd_291348 < baseStart_291348 := by decide
  rcases family_descends (prefixWord ++ tailWord_291348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291381 : List Nat := [1, 3, 3, 1, 1, 2, 1, 5, 6]
def baseStart_291381 : Nat := 118140960795 + 291381 * 2 ^ 59
def prefixEnd_291381 : Nat := 4983230072969 + 3 ^ 40 * 291381 * 2
def baseEnd_291381 : Nat := 16624278509758856021941

theorem tailTrace_291381 : CollatzResearch.WordTrace tailWord_291381 prefixEnd_291381 16624278509758856021941 := by
  unfold tailWord_291381
  simp only [CollatzResearch.WordTrace]
  refine ⟨10627538157383875758001997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7085025438255917172001331 10627538157383875758001997)
  ·
    refine ⟨3985326809018953409250749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10627538157383875758001997 3985326809018953409250749)
    ·
      refine ⟨1494497553382107528469031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3985326809018953409250749 1494497553382107528469031)
      ·
        refine ⟨2241746330073161292703547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1494497553382107528469031 2241746330073161292703547)
        ·
          refine ⟨3362619495109741939055321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2241746330073161292703547 3362619495109741939055321)
          ·
            refine ⟨2521964621332306454291491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3362619495109741939055321 2521964621332306454291491)
            ·
              refine ⟨3782946931998459681437237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2521964621332306454291491 3782946931998459681437237)
              ·
                refine ⟨354651274874855595134741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3782946931998459681437237 354651274874855595134741)
                ·
                  refine ⟨16624278509758856021941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 354651274874855595134741 16624278509758856021941)
                  ·
                    rfl

theorem cell23_291381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 6].length) (baseStart_291381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291381 prefixEnd_291381 := by exact prefixLift 291381
  have htrace : WordTrace (prefixWord ++ tailWord_291381) baseStart_291381 baseEnd_291381 := by
    simpa [prefixWord, tailWord_291381, baseEnd_291381] using wordTrace_append hprefix tailTrace_291381
  have hstable : (prefixWord ++ tailWord_291381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291381).length < 2 ^ (prefixWord ++ tailWord_291381).sum := by decide
  have hdescent : baseEnd_291381 < baseStart_291381 := by decide
  rcases family_descends (prefixWord ++ tailWord_291381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291425 : List Nat := [1, 2, 3, 1, 1, 5, 2, 1, 3, 1, 3]
def baseStart_291425 : Nat := 118140960795 + 291425 * 2 ^ 59
def prefixEnd_291425 : Nat := 4983230072969 + 3 ^ 40 * 291425 * 2
def baseEnd_291425 : Nat := 149641099736627532047267

theorem tailTrace_291425 : CollatzResearch.WordTrace tailWord_291425 prefixEnd_291425 149641099736627532047267 := by
  unfold tailWord_291425
  simp only [CollatzResearch.WordTrace]
  refine ⟨10629142969224471272603729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7086095312816314181735819 10629142969224471272603729)
  ·
    refine ⟨7971857226918353454452797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10629142969224471272603729 7971857226918353454452797)
    ·
      refine ⟨2989446460094382545419799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7971857226918353454452797 2989446460094382545419799)
      ·
        refine ⟨4484169690141573818129699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2989446460094382545419799 4484169690141573818129699)
        ·
          refine ⟨6726254535212360727194549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4484169690141573818129699 6726254535212360727194549)
          ·
            refine ⟨630586362676158818174489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6726254535212360727194549 630586362676158818174489)
            ·
              refine ⟨472939772007119113630867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 630586362676158818174489 472939772007119113630867)
              ·
                refine ⟨709409658010678670446301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 472939772007119113630867 709409658010678670446301)
                ·
                  refine ⟨266028621754004501417363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 709409658010678670446301 266028621754004501417363)
                  ·
                    refine ⟨399042932631006752126045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 266028621754004501417363 399042932631006752126045)
                    ·
                      refine ⟨149641099736627532047267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 399042932631006752126045 149641099736627532047267)
                      ·
                        rfl

theorem cell23_291425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_291425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291425 prefixEnd_291425 := by exact prefixLift 291425
  have htrace : WordTrace (prefixWord ++ tailWord_291425) baseStart_291425 baseEnd_291425 := by
    simpa [prefixWord, tailWord_291425, baseEnd_291425] using wordTrace_append hprefix tailTrace_291425
  have hstable : (prefixWord ++ tailWord_291425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291425).length < 2 ^ (prefixWord ++ tailWord_291425).sum := by decide
  have hdescent : baseEnd_291425 < baseStart_291425 := by decide
  rcases family_descends (prefixWord ++ tailWord_291425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291476 : List Nat := [2, 4, 2, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_291476 : Nat := 118140960795 + 291476 * 2 ^ 59
def prefixEnd_291476 : Nat := 4983230072969 + 3 ^ 40 * 291476 * 2
def baseEnd_291476 : Nat := 149667287250006832509533

theorem tailTrace_291476 : CollatzResearch.WordTrace tailWord_291476 prefixEnd_291476 149667287250006832509533 := by
  unfold tailWord_291476
  simp only [CollatzResearch.WordTrace]
  refine ⟨5315501546019853491355141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7087335394693137988473521 5315501546019853491355141)
  ·
    refine ⟨996656539878722529629089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5315501546019853491355141 996656539878722529629089)
    ·
      refine ⟨747492404909041897221817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 996656539878722529629089 747492404909041897221817)
      ·
        refine ⟨560619303681781422916363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 747492404909041897221817 560619303681781422916363)
        ·
          refine ⟨840928955522672134374545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560619303681781422916363 840928955522672134374545)
          ·
            refine ⟨630696716642004100780909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 840928955522672134374545 630696716642004100780909)
            ·
              refine ⟨236511268740751537792841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 630696716642004100780909 236511268740751537792841)
              ·
                refine ⟨177383451555563653344631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236511268740751537792841 177383451555563653344631)
                ·
                  refine ⟨266075177333345480016947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177383451555563653344631 266075177333345480016947)
                  ·
                    refine ⟨399112766000018220025421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 266075177333345480016947 399112766000018220025421)
                    ·
                      refine ⟨149667287250006832509533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 399112766000018220025421 149667287250006832509533)
                      ·
                        rfl

theorem cell23_291476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_291476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291476 prefixEnd_291476 := by exact prefixLift 291476
  have htrace : WordTrace (prefixWord ++ tailWord_291476) baseStart_291476 baseEnd_291476 := by
    simpa [prefixWord, tailWord_291476, baseEnd_291476] using wordTrace_append hprefix tailTrace_291476
  have hstable : (prefixWord ++ tailWord_291476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291476).length < 2 ^ (prefixWord ++ tailWord_291476).sum := by decide
  have hdescent : baseEnd_291476 < baseStart_291476 := by decide
  rcases family_descends (prefixWord ++ tailWord_291476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291488 : List Nat := [2, 1, 1, 4, 4, 1, 2, 8]
def baseStart_291488 : Nat := 118140960795 + 291488 * 2 ^ 59
def prefixEnd_291488 : Nat := 4983230072969 + 3 ^ 40 * 291488 * 2
def baseEnd_291488 : Nat := 5543461074735584650351

theorem tailTrace_291488 : CollatzResearch.WordTrace tailWord_291488 prefixEnd_291488 5543461074735584650351 := by
  unfold tailWord_291488
  simp only [CollatzResearch.WordTrace]
  refine ⟨5315720383998116516073559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7087627178664155354764745 5315720383998116516073559)
  ·
    refine ⟨7973580575997174774110339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5315720383998116516073559 7973580575997174774110339)
    ·
      refine ⟨11960370863995762161165509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7973580575997174774110339 11960370863995762161165509)
      ·
        refine ⟨2242569536999205405218533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11960370863995762161165509 2242569536999205405218533)
        ·
          refine ⟨420481788187351013478475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2242569536999205405218533 420481788187351013478475)
          ·
            refine ⟨630722682281026520217713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420481788187351013478475 630722682281026520217713)
            ·
              refine ⟨473042011710769890163285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 630722682281026520217713 473042011710769890163285)
              ·
                refine ⟨5543461074735584650351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 473042011710769890163285 5543461074735584650351)
                ·
                  rfl

theorem cell23_291488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 8].length) (baseStart_291488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291488 prefixEnd_291488 := by exact prefixLift 291488
  have htrace : WordTrace (prefixWord ++ tailWord_291488) baseStart_291488 baseEnd_291488 := by
    simpa [prefixWord, tailWord_291488, baseEnd_291488] using wordTrace_append hprefix tailTrace_291488
  have hstable : (prefixWord ++ tailWord_291488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291488).length < 2 ^ (prefixWord ++ tailWord_291488).sum := by decide
  have hdescent : baseEnd_291488 < baseStart_291488 := by decide
  rcases family_descends (prefixWord ++ tailWord_291488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291502 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_291502 : Nat := 118140960795 + 291502 * 2 ^ 59
def prefixEnd_291502 : Nat := 4983230072969 + 3 ^ 40 * 291502 * 2
def baseEnd_291502 : Nat := 149680637747023730784413

theorem tailTrace_291502 : CollatzResearch.WordTrace tailWord_291502 prefixEnd_291502 149680637747023730784413 := by
  unfold tailWord_291502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1328993923743189177894595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7087967593297008948771173 1328993923743189177894595)
  ·
    refine ⟨1993490885614783766841893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1328993923743189177894595 1993490885614783766841893)
    ·
      refine ⟨373779541052771956282855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1993490885614783766841893 373779541052771956282855)
      ·
        refine ⟨560669311579157934424283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373779541052771956282855 560669311579157934424283)
        ·
          refine ⟨841003967368736901636425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560669311579157934424283 841003967368736901636425)
          ·
            refine ⟨630752975526552676227319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 841003967368736901636425 630752975526552676227319)
            ·
              refine ⟨946129463289829014340979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630752975526552676227319 946129463289829014340979)
              ·
                refine ⟨1419194194934743521511469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 946129463289829014340979 1419194194934743521511469)
                ·
                  refine ⟨532197823100528820566801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1419194194934743521511469 532197823100528820566801)
                  ·
                    refine ⟨399148367325396615425101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 532197823100528820566801 399148367325396615425101)
                    ·
                      refine ⟨149680637747023730784413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 399148367325396615425101 149680637747023730784413)
                      ·
                        rfl

theorem cell23_291502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_291502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291502 prefixEnd_291502 := by exact prefixLift 291502
  have htrace : WordTrace (prefixWord ++ tailWord_291502) baseStart_291502 baseEnd_291502 := by
    simpa [prefixWord, tailWord_291502, baseEnd_291502] using wordTrace_append hprefix tailTrace_291502
  have hstable : (prefixWord ++ tailWord_291502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291502).length < 2 ^ (prefixWord ++ tailWord_291502).sum := by decide
  have hdescent : baseEnd_291502 < baseStart_291502 := by decide
  rcases family_descends (prefixWord ++ tailWord_291502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291526 : List Nat := [6, 1, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_291526 : Nat := 118140960795 + 291526 * 2 ^ 59
def prefixEnd_291526 : Nat := 4983230072969 + 3 ^ 40 * 291526 * 2
def baseEnd_291526 : Nat := 49897653760910545628101

theorem tailTrace_291526 : CollatzResearch.WordTrace tailWord_291526 prefixEnd_291526 49897653760910545628101 := by
  unfold tailWord_291526
  simp only [CollatzResearch.WordTrace]
  refine ⟨332275835683080172563451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7088551161239043681353621 332275835683080172563451)
  ·
    refine ⟨498413753524620258845177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 332275835683080172563451 498413753524620258845177)
    ·
      refine ⟨373810315143465194133883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 498413753524620258845177 373810315143465194133883)
      ·
        refine ⟨560715472715197791200825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373810315143465194133883 560715472715197791200825)
        ·
          refine ⟨420536604536398343400619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 560715472715197791200825 420536604536398343400619)
          ·
            refine ⟨630804906804597515100929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420536604536398343400619 630804906804597515100929)
            ·
              refine ⟨473103680103448136325697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 630804906804597515100929 473103680103448136325697)
              ·
                refine ⟨354827760077586102244273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 473103680103448136325697 354827760077586102244273)
                ·
                  refine ⟨266120820058189576683205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 354827760077586102244273 266120820058189576683205)
                  ·
                    refine ⟨49897653760910545628101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 266120820058189576683205 49897653760910545628101)
                    ·
                      rfl

theorem cell23_291526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_291526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291526 prefixEnd_291526 := by exact prefixLift 291526
  have htrace : WordTrace (prefixWord ++ tailWord_291526) baseStart_291526 baseEnd_291526 := by
    simpa [prefixWord, tailWord_291526, baseEnd_291526] using wordTrace_append hprefix tailTrace_291526
  have hstable : (prefixWord ++ tailWord_291526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291526).length < 2 ^ (prefixWord ++ tailWord_291526).sum := by decide
  have hdescent : baseEnd_291526 < baseStart_291526 := by decide
  rcases family_descends (prefixWord ++ tailWord_291526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291532 : List Nat := [2, 2, 1, 5, 1, 1, 1, 4, 2, 1, 3]
def baseStart_291532 : Nat := 118140960795 + 291532 * 2 ^ 59
def prefixEnd_291532 : Nat := 4983230072969 + 3 ^ 40 * 291532 * 2
def baseEnd_291532 : Nat := 149696042166658613409275

theorem tailTrace_291532 : CollatzResearch.WordTrace tailWord_291532 prefixEnd_291532 149696042166658613409275 := by
  unfold tailWord_291532
  simp only [CollatzResearch.WordTrace]
  refine ⟨5316522789918414273374425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7088697053224552364499233 5316522789918414273374425)
  ·
    refine ⟨3987392092438810705030819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5316522789918414273374425 3987392092438810705030819)
    ·
      refine ⟨5981088138658216057546229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3987392092438810705030819 5981088138658216057546229)
      ·
        refine ⟨560727012999207755394959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5981088138658216057546229 560727012999207755394959)
        ·
          refine ⟨841090519498811633092439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560727012999207755394959 841090519498811633092439)
          ·
            refine ⟨1261635779248217449638659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841090519498811633092439 1261635779248217449638659)
            ·
              refine ⟨1892453668872326174457989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1261635779248217449638659 1892453668872326174457989)
              ·
                refine ⟨354835062913561157710873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1892453668872326174457989 354835062913561157710873)
                ·
                  refine ⟨266126297185170868283155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 354835062913561157710873 266126297185170868283155)
                  ·
                    refine ⟨399189445777756302424733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 266126297185170868283155 399189445777756302424733)
                    ·
                      refine ⟨149696042166658613409275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 399189445777756302424733 149696042166658613409275)
                      ·
                        rfl

theorem cell23_291532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_291532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291532 prefixEnd_291532 := by exact prefixLift 291532
  have htrace : WordTrace (prefixWord ++ tailWord_291532) baseStart_291532 baseEnd_291532 := by
    simpa [prefixWord, tailWord_291532, baseEnd_291532] using wordTrace_append hprefix tailTrace_291532
  have hstable : (prefixWord ++ tailWord_291532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291532).length < 2 ^ (prefixWord ++ tailWord_291532).sum := by decide
  have hdescent : baseEnd_291532 < baseStart_291532 := by decide
  rcases family_descends (prefixWord ++ tailWord_291532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291533 : List Nat := [1, 6, 2, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_291533 : Nat := 118140960795 + 291533 * 2 ^ 59
def prefixEnd_291533 : Nat := 4983230072969 + 3 ^ 40 * 291533 * 2
def baseEnd_291533 : Nat := 149696555647313109496771

theorem tailTrace_291533 : CollatzResearch.WordTrace tailWord_291533 prefixEnd_291533 149696555647313109496771 := by
  unfold tailWord_291533
  simp only [CollatzResearch.WordTrace]
  refine ⟨10633082052833205717535253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7088721368555470478356835 10633082052833205717535253)
  ·
    refine ⟨498425721226556518009465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10633082052833205717535253 498425721226556518009465)
    ·
      refine ⟨373819290919917388507099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 498425721226556518009465 373819290919917388507099)
      ·
        refine ⟨560728936379876082760649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373819290919917388507099 560728936379876082760649)
        ·
          refine ⟨420546702284907062070487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 560728936379876082760649 420546702284907062070487)
          ·
            refine ⟨630820053427360593105731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420546702284907062070487 630820053427360593105731)
            ·
              refine ⟨946230080141040889658597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630820053427360593105731 946230080141040889658597)
              ·
                refine ⟨177418140026445166810987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 946230080141040889658597 177418140026445166810987)
                ·
                  refine ⟨266127210039667750216481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177418140026445166810987 266127210039667750216481)
                  ·
                    refine ⟨199595407529750812662361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 266127210039667750216481 199595407529750812662361)
                    ·
                      refine ⟨149696555647313109496771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 199595407529750812662361 149696555647313109496771)
                      ·
                        rfl

theorem cell23_291533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_291533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291533 prefixEnd_291533 := by exact prefixLift 291533
  have htrace : WordTrace (prefixWord ++ tailWord_291533) baseStart_291533 baseEnd_291533 := by
    simpa [prefixWord, tailWord_291533, baseEnd_291533] using wordTrace_append hprefix tailTrace_291533
  have hstable : (prefixWord ++ tailWord_291533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291533).length < 2 ^ (prefixWord ++ tailWord_291533).sum := by decide
  have hdescent : baseEnd_291533 < baseStart_291533 := by decide
  rcases family_descends (prefixWord ++ tailWord_291533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291561 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 9]
def baseStart_291561 : Nat := 118140960795 + 291561 * 2 ^ 59
def prefixEnd_291561 : Nat := 4983230072969 + 3 ^ 40 * 291561 * 2
def baseEnd_291561 : Nat := 16634548122848777771849

theorem tailTrace_291561 : CollatzResearch.WordTrace tailWord_291561 prefixEnd_291561 16634548122848777771849 := by
  unfold tailWord_291561
  simp only [CollatzResearch.WordTrace]
  refine ⟨10634103296731766499554537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7089402197821177666369691 10634103296731766499554537)
  ·
    refine ⟨7975577472548824874665903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10634103296731766499554537 7975577472548824874665903)
    ·
      refine ⟨11963366208823237311998855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7975577472548824874665903 11963366208823237311998855)
      ·
        refine ⟨17945049313234855967998283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11963366208823237311998855 17945049313234855967998283)
        ·
          refine ⟨26917573969852283951997425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17945049313234855967998283 26917573969852283951997425)
          ·
            refine ⟨20188180477389212963998069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26917573969852283951997425 20188180477389212963998069)
            ·
              refine ⟨1892641919755238715374819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20188180477389212963998069 1892641919755238715374819)
              ·
                refine ⟨2838962879632858073062229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1892641919755238715374819 2838962879632858073062229)
                ·
                  refine ⟨16634548122848777771849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2838962879632858073062229 16634548122848777771849)
                  ·
                    rfl

theorem cell23_291561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 9].length) (baseStart_291561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291561 prefixEnd_291561 := by exact prefixLift 291561
  have htrace : WordTrace (prefixWord ++ tailWord_291561) baseStart_291561 baseEnd_291561 := by
    simpa [prefixWord, tailWord_291561, baseEnd_291561] using wordTrace_append hprefix tailTrace_291561
  have hstable : (prefixWord ++ tailWord_291561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291561).length < 2 ^ (prefixWord ++ tailWord_291561).sum := by decide
  have hdescent : baseEnd_291561 < baseStart_291561 := by decide
  rcases family_descends (prefixWord ++ tailWord_291561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291571 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 7]
def baseStart_291571 : Nat := 118140960795 + 291571 * 2 ^ 59
def prefixEnd_291571 : Nat := 4983230072969 + 3 ^ 40 * 291571 * 2
def baseEnd_291571 : Nat := 149716067912183960821595

theorem tailTrace_291571 : CollatzResearch.WordTrace tailWord_291571 prefixEnd_291571 149716067912183960821595 := by
  unfold tailWord_291571
  simp only [CollatzResearch.WordTrace]
  refine ⟨10634468026695538207418567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7089645351130358804945711 10634468026695538207418567)
  ·
    refine ⟨15951702040043307311127851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10634468026695538207418567 15951702040043307311127851)
    ·
      refine ⟨23927553060064960966691777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15951702040043307311127851 23927553060064960966691777)
      ·
        refine ⟨17945664795048720725018833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23927553060064960966691777 17945664795048720725018833)
        ·
          refine ⟨13459248596286540543764125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17945664795048720725018833 13459248596286540543764125)
          ·
            refine ⟨5047218223607452703911547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13459248596286540543764125 5047218223607452703911547)
            ·
              refine ⟨7570827335411179055867321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5047218223607452703911547 7570827335411179055867321)
              ·
                refine ⟨5678120501558384291900491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7570827335411179055867321 5678120501558384291900491)
                ·
                  refine ⟨8517180752337576437850737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5678120501558384291900491 8517180752337576437850737)
                  ·
                    refine ⟨6387885564253182328388053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8517180752337576437850737 6387885564253182328388053)
                    ·
                      refine ⟨149716067912183960821595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6387885564253182328388053 149716067912183960821595)
                      ·
                        rfl

theorem cell23_291571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_291571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291571 prefixEnd_291571 := by exact prefixLift 291571
  have htrace : WordTrace (prefixWord ++ tailWord_291571) baseStart_291571 baseEnd_291571 := by
    simpa [prefixWord, tailWord_291571, baseEnd_291571] using wordTrace_append hprefix tailTrace_291571
  have hstable : (prefixWord ++ tailWord_291571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291571).length < 2 ^ (prefixWord ++ tailWord_291571).sum := by decide
  have hdescent : baseEnd_291571 < baseStart_291571 := by decide
  rcases family_descends (prefixWord ++ tailWord_291571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291628 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 4]
def baseStart_291628 : Nat := 118140960795 + 291628 * 2 ^ 59
def prefixEnd_291628 : Nat := 4983230072969 + 3 ^ 40 * 291628 * 2
def baseEnd_291628 : Nat := 149745336309490237808833

theorem tailTrace_291628 : CollatzResearch.WordTrace tailWord_291628 prefixEnd_291628 149745336309490237808833 := by
  unfold tailWord_291628
  simp only [CollatzResearch.WordTrace]
  refine ⟨5318273493744518471121769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7091031324992691294829025 5318273493744518471121769)
  ·
    refine ⟨3988705120308388853341327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5318273493744518471121769 3988705120308388853341327)
    ·
      refine ⟨5983057680462583280011991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3988705120308388853341327 5983057680462583280011991)
      ·
        refine ⟨8974586520693874920017987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5983057680462583280011991 8974586520693874920017987)
        ·
          refine ⟨13461879781040812380026981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8974586520693874920017987 13461879781040812380026981)
          ·
            refine ⟨2524102458945152321255059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13461879781040812380026981 2524102458945152321255059)
            ·
              refine ⟨3786153688417728481882589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2524102458945152321255059 3786153688417728481882589)
              ·
                refine ⟨1419807633156648180705971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3786153688417728481882589 1419807633156648180705971)
                ·
                  refine ⟨2129711449734972271058957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1419807633156648180705971 2129711449734972271058957)
                  ·
                    refine ⟨798641793650614601647109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2129711449734972271058957 798641793650614601647109)
                    ·
                      refine ⟨149745336309490237808833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 798641793650614601647109 149745336309490237808833)
                      ·
                        rfl

theorem cell23_291628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_291628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291628 prefixEnd_291628 := by exact prefixLift 291628
  have htrace : WordTrace (prefixWord ++ tailWord_291628) baseStart_291628 baseEnd_291628 := by
    simpa [prefixWord, tailWord_291628, baseEnd_291628] using wordTrace_append hprefix tailTrace_291628
  have hstable : (prefixWord ++ tailWord_291628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291628).length < 2 ^ (prefixWord ++ tailWord_291628).sum := by decide
  have hdescent : baseEnd_291628 < baseStart_291628 := by decide
  rcases family_descends (prefixWord ++ tailWord_291628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291658 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_291658 : Nat := 118140960795 + 291658 * 2 ^ 59
def prefixEnd_291658 : Nat := 4983230072969 + 3 ^ 40 * 291658 * 2
def baseEnd_291658 : Nat := 149760740729125120433695

theorem tailTrace_291658 : CollatzResearch.WordTrace tailWord_291658 prefixEnd_291658 149760740729125120433695 := by
  unfold tailWord_291658
  simp only [CollatzResearch.WordTrace]
  refine ⟨2659410294345088016458907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7091760784920234710557085 2659410294345088016458907)
  ·
    refine ⟨3989115441517632024688361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2659410294345088016458907 3989115441517632024688361)
    ·
      refine ⟨2991836581138224018516271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3989115441517632024688361 2991836581138224018516271)
      ·
        refine ⟨4487754871707336027774407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2991836581138224018516271 4487754871707336027774407)
        ·
          refine ⟨6731632307561004041661611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4487754871707336027774407 6731632307561004041661611)
          ·
            refine ⟨10097448461341506062492417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6731632307561004041661611 10097448461341506062492417)
            ·
              refine ⟨7573086346006129546869313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10097448461341506062492417 7573086346006129546869313)
              ·
                refine ⟨5679814759504597160151985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7573086346006129546869313 5679814759504597160151985)
                ·
                  refine ⟨4259861069628447870113989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5679814759504597160151985 4259861069628447870113989)
                  ·
                    refine ⟨798723950555333975646373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4259861069628447870113989 798723950555333975646373)
                    ·
                      refine ⟨149760740729125120433695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 798723950555333975646373 149760740729125120433695)
                      ·
                        rfl

theorem cell23_291658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_291658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291658 prefixEnd_291658 := by exact prefixLift 291658
  have htrace : WordTrace (prefixWord ++ tailWord_291658) baseStart_291658 baseEnd_291658 := by
    simpa [prefixWord, tailWord_291658, baseEnd_291658] using wordTrace_append hprefix tailTrace_291658
  have hstable : (prefixWord ++ tailWord_291658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291658).length < 2 ^ (prefixWord ++ tailWord_291658).sum := by decide
  have hdescent : baseEnd_291658 < baseStart_291658 := by decide
  rcases family_descends (prefixWord ++ tailWord_291658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291702 : List Nat := [5, 1, 1, 3, 1, 1, 1, 4, 6]
def baseStart_291702 : Nat := 118140960795 + 291702 * 2 ^ 59
def prefixEnd_291702 : Nat := 4983230072969 + 3 ^ 40 * 291702 * 2
def baseEnd_291702 : Nat := 16642592653102549809277

theorem tailTrace_291702 : CollatzResearch.WordTrace tailWord_291702 prefixEnd_291702 16642592653102549809277 := by
  unfold tailWord_291702
  simp only [CollatzResearch.WordTrace]
  refine ⟨664952874326309223777335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7092830659480631720291573 664952874326309223777335)
  ·
    refine ⟨997429311489463835666003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 664952874326309223777335 997429311489463835666003)
    ·
      refine ⟨1496143967234195753499005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 997429311489463835666003 1496143967234195753499005)
      ·
        refine ⟨561053987712823407562127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1496143967234195753499005 561053987712823407562127)
        ·
          refine ⟨841580981569235111343191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561053987712823407562127 841580981569235111343191)
          ·
            refine ⟨1262371472353852667014787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841580981569235111343191 1262371472353852667014787)
            ·
              refine ⟨1893557208530779000522181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262371472353852667014787 1893557208530779000522181)
              ·
                refine ⟨355041976599521062597909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1893557208530779000522181 355041976599521062597909)
                ·
                  refine ⟨16642592653102549809277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 355041976599521062597909 16642592653102549809277)
                  ·
                    rfl

theorem cell23_291702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_291702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291702 prefixEnd_291702 := by exact prefixLift 291702
  have htrace : WordTrace (prefixWord ++ tailWord_291702) baseStart_291702 baseEnd_291702 := by
    simpa [prefixWord, tailWord_291702, baseEnd_291702] using wordTrace_append hprefix tailTrace_291702
  have hstable : (prefixWord ++ tailWord_291702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291702).length < 2 ^ (prefixWord ++ tailWord_291702).sum := by decide
  have hdescent : baseEnd_291702 < baseStart_291702 := by decide
  rcases family_descends (prefixWord ++ tailWord_291702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291708 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_291708 : Nat := 118140960795 + 291708 * 2 ^ 59
def prefixEnd_291708 : Nat := 4983230072969 + 3 ^ 40 * 291708 * 2
def baseEnd_291708 : Nat := 149786414761849924808465

theorem tailTrace_291708 : CollatzResearch.WordTrace tailWord_291708 prefixEnd_291708 149786414761849924808465 := by
  unfold tailWord_291708
  simp only [CollatzResearch.WordTrace]
  refine ⟨5319732413599605302577889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7092976551466140403437185 5319732413599605302577889)
  ·
    refine ⟨3989799310199703976933417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5319732413599605302577889 3989799310199703976933417)
    ·
      refine ⟨2992349482649777982700063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3989799310199703976933417 2992349482649777982700063)
      ·
        refine ⟨4488524223974666974050095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2992349482649777982700063 4488524223974666974050095)
        ·
          refine ⟨6732786335962000461075143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4488524223974666974050095 6732786335962000461075143)
          ·
            refine ⟨10099179503943000691612715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6732786335962000461075143 10099179503943000691612715)
            ·
              refine ⟨15148769255914501037419073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10099179503943000691612715 15148769255914501037419073)
              ·
                refine ⟨11361576941935875778064305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15148769255914501037419073 11361576941935875778064305)
                ·
                  refine ⟨8521182706451906833548229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11361576941935875778064305 8521182706451906833548229)
                  ·
                    refine ⟨1597721757459732531290293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8521182706451906833548229 1597721757459732531290293)
                    ·
                      refine ⟨149786414761849924808465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1597721757459732531290293 149786414761849924808465)
                      ·
                        rfl

theorem cell23_291708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_291708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291708 prefixEnd_291708 := by exact prefixLift 291708
  have htrace : WordTrace (prefixWord ++ tailWord_291708) baseStart_291708 baseEnd_291708 := by
    simpa [prefixWord, tailWord_291708, baseEnd_291708] using wordTrace_append hprefix tailTrace_291708
  have hstable : (prefixWord ++ tailWord_291708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291708).length < 2 ^ (prefixWord ++ tailWord_291708).sum := by decide
  have hdescent : baseEnd_291708 < baseStart_291708 := by decide
  rcases family_descends (prefixWord ++ tailWord_291708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291732 : List Nat := [2, 4, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_291732 : Nat := 118140960795 + 291732 * 2 ^ 59
def prefixEnd_291732 : Nat := 4983230072969 + 3 ^ 40 * 291732 * 2
def baseEnd_291732 : Nat := 49932912765852610302785

theorem tailTrace_291732 : CollatzResearch.WordTrace tailWord_291732 prefixEnd_291732 49932912765852610302785 := by
  unfold tailWord_291732
  simp only [CollatzResearch.WordTrace]
  refine ⟨5320170089556131352014725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7093560119408175136019633 5320170089556131352014725)
  ·
    refine ⟨997531891791774628502761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5320170089556131352014725 997531891791774628502761)
    ·
      refine ⟨748148918843830971377071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 997531891791774628502761 748148918843830971377071)
      ·
        refine ⟨1122223378265746457065607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 748148918843830971377071 1122223378265746457065607)
        ·
          refine ⟨1683335067398619685598411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1122223378265746457065607 1683335067398619685598411)
          ·
            refine ⟨2525002601097929528397617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1683335067398619685598411 2525002601097929528397617)
            ·
              refine ⟨1893751950823447146298213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2525002601097929528397617 1893751950823447146298213)
              ·
                refine ⟨355078490779396339930915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1893751950823447146298213 355078490779396339930915)
                ·
                  refine ⟨532617736169094509896373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355078490779396339930915 532617736169094509896373)
                  ·
                    refine ⟨49932912765852610302785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 532617736169094509896373 49932912765852610302785)
                    ·
                      rfl

theorem cell23_291732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_291732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291732 prefixEnd_291732 := by exact prefixLift 291732
  have htrace : WordTrace (prefixWord ++ tailWord_291732) baseStart_291732 baseEnd_291732 := by
    simpa [prefixWord, tailWord_291732, baseEnd_291732] using wordTrace_append hprefix tailTrace_291732
  have hstable : (prefixWord ++ tailWord_291732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291732).length < 2 ^ (prefixWord ++ tailWord_291732).sum := by decide
  have hdescent : baseEnd_291732 < baseStart_291732 := by decide
  rcases family_descends (prefixWord ++ tailWord_291732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291735 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 4]
def baseStart_291735 : Nat := 118140960795 + 291735 * 2 ^ 59
def prefixEnd_291735 : Nat := 4983230072969 + 3 ^ 40 * 291735 * 2
def baseEnd_291735 : Nat := 149800278739521319170841

theorem tailTrace_291735 : CollatzResearch.WordTrace tailWord_291735 prefixEnd_291735 149800278739521319170841 := by
  unfold tailWord_291735
  simp only [CollatzResearch.WordTrace]
  refine ⟨10640449598101394216388659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7093633065400929477592439 10640449598101394216388659)
  ·
    refine ⟨15960674397152091324582989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10640449598101394216388659 15960674397152091324582989)
    ·
      refine ⟨5985252898932034246718621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15960674397152091324582989 5985252898932034246718621)
      ·
        refine ⟨2244469837099512842519483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5985252898932034246718621 2244469837099512842519483)
        ·
          refine ⟨3366704755649269263779225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2244469837099512842519483 3366704755649269263779225)
          ·
            refine ⟨2525028566736951947834419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3366704755649269263779225 2525028566736951947834419)
            ·
              refine ⟨3787542850105427921751629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2525028566736951947834419 3787542850105427921751629)
              ·
                refine ⟨1420328568789535470656861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3787542850105427921751629 1420328568789535470656861)
                ·
                  refine ⟨532623213296075801496323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1420328568789535470656861 532623213296075801496323)
                  ·
                    refine ⟨798934819944113702244485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 532623213296075801496323 798934819944113702244485)
                    ·
                      refine ⟨149800278739521319170841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 798934819944113702244485 149800278739521319170841)
                      ·
                        rfl

theorem cell23_291735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_291735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291735 prefixEnd_291735 := by exact prefixLift 291735
  have htrace : WordTrace (prefixWord ++ tailWord_291735) baseStart_291735 baseEnd_291735 := by
    simpa [prefixWord, tailWord_291735, baseEnd_291735] using wordTrace_append hprefix tailTrace_291735
  have hstable : (prefixWord ++ tailWord_291735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291735).length < 2 ^ (prefixWord ++ tailWord_291735).sum := by decide
  have hdescent : baseEnd_291735 < baseStart_291735 := by decide
  rcases family_descends (prefixWord ++ tailWord_291735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291746 : List Nat := [3, 3, 1, 2, 2, 1, 1, 5, 1, 1, 3]
def baseStart_291746 : Nat := 118140960795 + 291746 * 2 ^ 59
def prefixEnd_291746 : Nat := 4983230072969 + 3 ^ 40 * 291746 * 2
def baseEnd_291746 : Nat := 149805927026720776133291

theorem tailTrace_291746 : CollatzResearch.WordTrace tailWord_291746 prefixEnd_291746 149805927026720776133291 := by
  unfold tailWord_291746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2660212700265385773759773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7093900534041028730026061 2660212700265385773759773)
  ·
    refine ⟨997579762599519665159915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2660212700265385773759773 997579762599519665159915)
    ·
      refine ⟨1496369643899279497739873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 997579762599519665159915 1496369643899279497739873)
      ·
        refine ⟨1122277232924459623304905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1496369643899279497739873 1122277232924459623304905)
        ·
          refine ⟨841707924693344717478679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1122277232924459623304905 841707924693344717478679)
          ·
            refine ⟨1262561887040017076218019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841707924693344717478679 1262561887040017076218019)
            ·
              refine ⟨1893842830560025614327029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262561887040017076218019 1893842830560025614327029)
              ·
                refine ⟨177547765365002401343159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1893842830560025614327029 177547765365002401343159)
                ·
                  refine ⟨266321648047503602014739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177547765365002401343159 266321648047503602014739)
                  ·
                    refine ⟨399482472071255403022109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 266321648047503602014739 399482472071255403022109)
                    ·
                      refine ⟨149805927026720776133291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 399482472071255403022109 149805927026720776133291)
                      ·
                        rfl

theorem cell23_291746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_291746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291746 prefixEnd_291746 := by exact prefixLift 291746
  have htrace : WordTrace (prefixWord ++ tailWord_291746) baseStart_291746 baseEnd_291746 := by
    simpa [prefixWord, tailWord_291746, baseEnd_291746] using wordTrace_append hprefix tailTrace_291746
  have hstable : (prefixWord ++ tailWord_291746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291746).length < 2 ^ (prefixWord ++ tailWord_291746).sum := by decide
  have hdescent : baseEnd_291746 < baseStart_291746 := by decide
  rcases family_descends (prefixWord ++ tailWord_291746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291765 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_291765 : Nat := 118140960795 + 291765 * 2 ^ 59
def prefixEnd_291765 : Nat := 4983230072969 + 3 ^ 40 * 291765 * 2
def baseEnd_291765 : Nat := 149815683159156201795703

theorem tailTrace_291765 : CollatzResearch.WordTrace tailWord_291765 prefixEnd_291765 149815683159156201795703 := by
  unfold tailWord_291765
  simp only [CollatzResearch.WordTrace]
  refine ⟨10641543787992709339980749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7094362525328472893320499 10641543787992709339980749)
  ·
    refine ⟨3990578920497266002492781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10641543787992709339980749 3990578920497266002492781)
    ·
      refine ⟨1496467095186474750934793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3990578920497266002492781 1496467095186474750934793)
      ·
        refine ⟨1122350321389856063201095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1496467095186474750934793 1122350321389856063201095)
        ·
          refine ⟨1683525482084784094801643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1122350321389856063201095 1683525482084784094801643)
          ·
            refine ⟨2525288223127176142202465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1683525482084784094801643 2525288223127176142202465)
            ·
              refine ⟨1893966167345382106651849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2525288223127176142202465 1893966167345382106651849)
              ·
                refine ⟨1420474625509036579988887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1893966167345382106651849 1420474625509036579988887)
                ·
                  refine ⟨2130711938263554869983331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1420474625509036579988887 2130711938263554869983331)
                  ·
                    refine ⟨3196067907395332304974997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2130711938263554869983331 3196067907395332304974997)
                    ·
                      refine ⟨149815683159156201795703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3196067907395332304974997 149815683159156201795703)
                      ·
                        rfl

theorem cell23_291765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_291765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291765 prefixEnd_291765 := by exact prefixLift 291765
  have htrace : WordTrace (prefixWord ++ tailWord_291765) baseStart_291765 baseEnd_291765 := by
    simpa [prefixWord, tailWord_291765, baseEnd_291765] using wordTrace_append hprefix tailTrace_291765
  have hstable : (prefixWord ++ tailWord_291765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291765).length < 2 ^ (prefixWord ++ tailWord_291765).sum := by decide
  have hdescent : baseEnd_291765 < baseStart_291765 := by decide
  rcases family_descends (prefixWord ++ tailWord_291765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291769 : List Nat := [1, 2, 1, 4, 2, 2, 1, 3, 3, 2, 2]
def baseStart_291769 : Nat := 118140960795 + 291769 * 2 ^ 59
def prefixEnd_291769 : Nat := 4983230072969 + 3 ^ 40 * 291769 * 2
def baseEnd_291769 : Nat := 149817737081774186145685

theorem tailTrace_291769 : CollatzResearch.WordTrace tailWord_291769 prefixEnd_291769 149817737081774186145685 := by
  unfold tailWord_291769
  simp only [CollatzResearch.WordTrace]
  refine ⟨10641689679978218023126361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7094459786652145348750907 10641689679978218023126361)
  ·
    refine ⟨7981267259983663517344771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10641689679978218023126361 7981267259983663517344771)
    ·
      refine ⟨11971900889975495276017157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7981267259983663517344771 11971900889975495276017157)
      ·
        refine ⟨2244731416870405364253217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11971900889975495276017157 2244731416870405364253217)
        ·
          refine ⟨1683548562652804023189913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2244731416870405364253217 1683548562652804023189913)
          ·
            refine ⟨1262661421989603017392435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1683548562652804023189913 1262661421989603017392435)
            ·
              refine ⟨1893992132984404526088653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262661421989603017392435 1893992132984404526088653)
              ·
                refine ⟨710247049869151697283245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1893992132984404526088653 710247049869151697283245)
                ·
                  refine ⟨266342643700931886481217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 710247049869151697283245 266342643700931886481217)
                  ·
                    refine ⟨199756982775698914860913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 266342643700931886481217 199756982775698914860913)
                    ·
                      refine ⟨149817737081774186145685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 199756982775698914860913 149817737081774186145685)
                      ·
                        rfl

theorem cell23_291769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_291769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291769 prefixEnd_291769 := by exact prefixLift 291769
  have htrace : WordTrace (prefixWord ++ tailWord_291769) baseStart_291769 baseEnd_291769 := by
    simpa [prefixWord, tailWord_291769, baseEnd_291769] using wordTrace_append hprefix tailTrace_291769
  have hstable : (prefixWord ++ tailWord_291769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291769).length < 2 ^ (prefixWord ++ tailWord_291769).sum := by decide
  have hdescent : baseEnd_291769 < baseStart_291769 := by decide
  rcases family_descends (prefixWord ++ tailWord_291769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291836 : List Nat := [2, 2, 2, 1, 2, 3, 4, 1, 2, 1, 3]
def baseStart_291836 : Nat := 118140960795 + 291836 * 2 ^ 59
def prefixEnd_291836 : Nat := 4983230072969 + 3 ^ 40 * 291836 * 2
def baseEnd_291836 : Nat := 149852140285625424007877

theorem tailTrace_291836 : CollatzResearch.WordTrace tailWord_291836 prefixEnd_291836 149852140285625424007877 := by
  unfold tailWord_291836
  simp only [CollatzResearch.WordTrace]
  refine ⟨5322066685367744232907681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7096088913823658977210241 5322066685367744232907681)
  ·
    refine ⟨3991550014025808174680761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5322066685367744232907681 3991550014025808174680761)
    ·
      refine ⟨2993662510519356131010571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3991550014025808174680761 2993662510519356131010571)
      ·
        refine ⟨4490493765779034196515857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2993662510519356131010571 4490493765779034196515857)
        ·
          refine ⟨3367870324334275647386893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4490493765779034196515857 3367870324334275647386893)
          ·
            refine ⟨1262951371625353367770085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3367870324334275647386893 1262951371625353367770085)
            ·
              refine ⟨236803382179753756456891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1262951371625353367770085 236803382179753756456891)
              ·
                refine ⟨355205073269630634685337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236803382179753756456891 355205073269630634685337)
                ·
                  refine ⟨266403804952222976014003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355205073269630634685337 266403804952222976014003)
                  ·
                    refine ⟨399605707428334464021005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 266403804952222976014003 399605707428334464021005)
                    ·
                      refine ⟨149852140285625424007877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 399605707428334464021005 149852140285625424007877)
                      ·
                        rfl

theorem cell23_291836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_291836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291836 prefixEnd_291836 := by exact prefixLift 291836
  have htrace : WordTrace (prefixWord ++ tailWord_291836) baseStart_291836 baseEnd_291836 := by
    simpa [prefixWord, tailWord_291836, baseEnd_291836] using wordTrace_append hprefix tailTrace_291836
  have hstable : (prefixWord ++ tailWord_291836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291836).length < 2 ^ (prefixWord ++ tailWord_291836).sum := by decide
  have hdescent : baseEnd_291836 < baseStart_291836 := by decide
  rcases family_descends (prefixWord ++ tailWord_291836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291845 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 4, 1, 5]
def baseStart_291845 : Nat := 118140960795 + 291845 * 2 ^ 59
def prefixEnd_291845 : Nat := 4983230072969 + 3 ^ 40 * 291845 * 2
def baseEnd_291845 : Nat := 149856761611515888795335

theorem tailTrace_291845 : CollatzResearch.WordTrace tailWord_291845 prefixEnd_291845 149856761611515888795335 := by
  unfold tailWord_291845
  simp only [CollatzResearch.WordTrace]
  refine ⟨10644461627702883002892989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7096307751801922001928659 10644461627702883002892989)
  ·
    refine ⟨3991673110388581126084871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10644461627702883002892989 3991673110388581126084871)
    ·
      refine ⟨5987509665582871689127307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3991673110388581126084871 5987509665582871689127307)
      ·
        refine ⟨8981264498374307533690961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5987509665582871689127307 8981264498374307533690961)
        ·
          refine ⟨6735948373780730650268221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8981264498374307533690961 6735948373780730650268221)
          ·
            refine ⟨2525980640167773993850583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6735948373780730650268221 2525980640167773993850583)
            ·
              refine ⟨3788970960251660990775875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2525980640167773993850583 3788970960251660990775875)
              ·
                refine ⟨5683456440377491486163813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3788970960251660990775875 5683456440377491486163813)
                ·
                  refine ⟨1065648082570779653655715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5683456440377491486163813 1065648082570779653655715)
                  ·
                    refine ⟨1598472123856169480483573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1065648082570779653655715 1598472123856169480483573)
                    ·
                      refine ⟨149856761611515888795335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1598472123856169480483573 149856761611515888795335)
                      ·
                        rfl

theorem cell23_291845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_291845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291845 prefixEnd_291845 := by exact prefixLift 291845
  have htrace : WordTrace (prefixWord ++ tailWord_291845) baseStart_291845 baseEnd_291845 := by
    simpa [prefixWord, tailWord_291845, baseEnd_291845] using wordTrace_append hprefix tailTrace_291845
  have hstable : (prefixWord ++ tailWord_291845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291845).length < 2 ^ (prefixWord ++ tailWord_291845).sum := by decide
  have hdescent : baseEnd_291845 < baseStart_291845 := by decide
  rcases family_descends (prefixWord ++ tailWord_291845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291863 : List Nat := [1, 1, 3, 5, 1, 2, 3, 1, 1, 3, 2]
def baseStart_291863 : Nat := 118140960795 + 291863 * 2 ^ 59
def prefixEnd_291863 : Nat := 4983230072969 + 3 ^ 40 * 291863 * 2
def baseEnd_291863 : Nat := 149866004263296818370253

theorem tailTrace_291863 : CollatzResearch.WordTrace tailWord_291863 prefixEnd_291863 149866004263296818370253 := by
  unfold tailWord_291863
  simp only [CollatzResearch.WordTrace]
  refine ⟨10645118141637672077048243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7096745427758448051365495 10645118141637672077048243)
  ·
    refine ⟨15967677212456508115572365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10645118141637672077048243 15967677212456508115572365)
    ·
      refine ⟨5987878954671190543339637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15967677212456508115572365 5987878954671190543339637)
      ·
        refine ⟨561363652000424113438091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5987878954671190543339637 561363652000424113438091)
        ·
          refine ⟨842045478000636170157137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561363652000424113438091 842045478000636170157137)
          ·
            refine ⟨631534108500477127617853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 842045478000636170157137 631534108500477127617853)
            ·
              refine ⟨236825290687678922856695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 631534108500477127617853 236825290687678922856695)
              ·
                refine ⟨355237936031518384285043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236825290687678922856695 355237936031518384285043)
                ·
                  refine ⟨532856904047277576427565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355237936031518384285043 532856904047277576427565)
                  ·
                    refine ⟨199821339017729091160337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 532856904047277576427565 199821339017729091160337)
                    ·
                      refine ⟨149866004263296818370253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 199821339017729091160337 149866004263296818370253)
                      ·
                        rfl

theorem cell23_291863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_291863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291863 prefixEnd_291863 := by exact prefixLift 291863
  have htrace : WordTrace (prefixWord ++ tailWord_291863) baseStart_291863 baseEnd_291863 := by
    simpa [prefixWord, tailWord_291863, baseEnd_291863] using wordTrace_append hprefix tailTrace_291863
  have hstable : (prefixWord ++ tailWord_291863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291863).length < 2 ^ (prefixWord ++ tailWord_291863).sum := by decide
  have hdescent : baseEnd_291863 < baseStart_291863 := by decide
  rcases family_descends (prefixWord ++ tailWord_291863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291879 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_291879 : Nat := 118140960795 + 291879 * 2 ^ 59
def prefixEnd_291879 : Nat := 4983230072969 + 3 ^ 40 * 291879 * 2
def baseEnd_291879 : Nat := 149874219953768755770179

theorem tailTrace_291879 : CollatzResearch.WordTrace tailWord_291879 prefixEnd_291879 149874219953768755770179 := by
  unfold tailWord_291879
  simp only [CollatzResearch.WordTrace]
  refine ⟨10645701709579706809630691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7097134473053137873087127 10645701709579706809630691)
  ·
    refine ⟨15968552564369560214446037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10645701709579706809630691 15968552564369560214446037)
    ·
      refine ⟨374262950727411567526079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 15968552564369560214446037 374262950727411567526079)
      ·
        refine ⟨561394426091117351289119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374262950727411567526079 561394426091117351289119)
        ·
          refine ⟨842091639136676026933679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561394426091117351289119 842091639136676026933679)
          ·
            refine ⟨1263137458705014040400519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842091639136676026933679 1263137458705014040400519)
            ·
              refine ⟨1894706188057521060600779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263137458705014040400519 1894706188057521060600779)
              ·
                refine ⟨2842059282086281590901169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894706188057521060600779 2842059282086281590901169)
                ·
                  refine ⟨2131544461564711193175877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2842059282086281590901169 2131544461564711193175877)
                  ·
                    refine ⟨399664586543383348720477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2131544461564711193175877 399664586543383348720477)
                    ·
                      refine ⟨149874219953768755770179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 399664586543383348720477 149874219953768755770179)
                      ·
                        rfl

theorem cell23_291879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_291879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291879 prefixEnd_291879 := by exact prefixLift 291879
  have htrace : WordTrace (prefixWord ++ tailWord_291879) baseStart_291879 baseEnd_291879 := by
    simpa [prefixWord, tailWord_291879, baseEnd_291879] using wordTrace_append hprefix tailTrace_291879
  have hstable : (prefixWord ++ tailWord_291879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291879).length < 2 ^ (prefixWord ++ tailWord_291879).sum := by decide
  have hdescent : baseEnd_291879 < baseStart_291879 := by decide
  rcases family_descends (prefixWord ++ tailWord_291879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291895 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 1, 7]
def baseStart_291895 : Nat := 118140960795 + 291895 * 2 ^ 59
def prefixEnd_291895 : Nat := 4983230072969 + 3 ^ 40 * 291895 * 2
def baseEnd_291895 : Nat := 49960811881413564390035

theorem tailTrace_291895 : CollatzResearch.WordTrace tailWord_291895 prefixEnd_291895 49960811881413564390035 := by
  unfold tailWord_291895
  simp only [CollatzResearch.WordTrace]
  refine ⟨10646285277521741542213139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7097523518347827694808759 10646285277521741542213139)
  ·
    refine ⟨15969427916282612313319709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10646285277521741542213139 15969427916282612313319709)
    ·
      refine ⟨5988535468605979617494891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15969427916282612313319709 5988535468605979617494891)
      ·
        refine ⟨8982803202908969426242337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5988535468605979617494891 8982803202908969426242337)
        ·
          refine ⟨6737102402181727069681753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8982803202908969426242337 6737102402181727069681753)
          ·
            refine ⟨5052826801636295302261315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6737102402181727069681753 5052826801636295302261315)
            ·
              refine ⟨7579240202454442953391973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5052826801636295302261315 7579240202454442953391973)
              ·
                refine ⟨1421107537960208053760995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7579240202454442953391973 1421107537960208053760995)
                ·
                  refine ⟨2131661306940312080641493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421107537960208053760995 2131661306940312080641493)
                  ·
                    refine ⟨49960811881413564390035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2131661306940312080641493 49960811881413564390035)
                    ·
                      rfl

theorem cell23_291895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_291895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291895 prefixEnd_291895 := by exact prefixLift 291895
  have htrace : WordTrace (prefixWord ++ tailWord_291895) baseStart_291895 baseEnd_291895 := by
    simpa [prefixWord, tailWord_291895, baseEnd_291895] using wordTrace_append hprefix tailTrace_291895
  have hstable : (prefixWord ++ tailWord_291895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291895).length < 2 ^ (prefixWord ++ tailWord_291895).sum := by decide
  have hdescent : baseEnd_291895 < baseStart_291895 := by decide
  rcases family_descends (prefixWord ++ tailWord_291895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291952 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 3]
def baseStart_291952 : Nat := 118140960795 + 291952 * 2 ^ 59
def prefixEnd_291952 : Nat := 4983230072969 + 3 ^ 40 * 291952 * 2
def baseEnd_291952 : Nat := 149911704041546970157343

theorem tailTrace_291952 : CollatzResearch.WordTrace tailWord_291952 prefixEnd_291952 149911704041546970157343 := by
  unfold tailWord_291952
  simp only [CollatzResearch.WordTrace]
  refine ⟨5324182119157620138519055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7098909492210160184692073 5324182119157620138519055)
  ·
    refine ⟨7986273178736430207778583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5324182119157620138519055 7986273178736430207778583)
    ·
      refine ⟨11979409768104645311667875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7986273178736430207778583 11979409768104645311667875)
      ·
        refine ⟨17969114652156967967501813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11979409768104645311667875 17969114652156967967501813)
        ·
          refine ⟨1684604498639715746953295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17969114652156967967501813 1684604498639715746953295)
          ·
            refine ⟨2526906747959573620429943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1684604498639715746953295 2526906747959573620429943)
            ·
              refine ⟨3790360121939360430644915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2526906747959573620429943 3790360121939360430644915)
              ·
                refine ⟨5685540182909040645967373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3790360121939360430644915 5685540182909040645967373)
                ·
                  refine ⟨2132077568590890242237765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5685540182909040645967373 2132077568590890242237765)
                  ·
                    refine ⟨399764544110791920419581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2132077568590890242237765 399764544110791920419581)
                    ·
                      refine ⟨149911704041546970157343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 399764544110791920419581 149911704041546970157343)
                      ·
                        rfl

theorem cell23_291952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 3].length) (baseStart_291952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291952 prefixEnd_291952 := by exact prefixLift 291952
  have htrace : WordTrace (prefixWord ++ tailWord_291952) baseStart_291952 baseEnd_291952 := by
    simpa [prefixWord, tailWord_291952, baseEnd_291952] using wordTrace_append hprefix tailTrace_291952
  have hstable : (prefixWord ++ tailWord_291952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291952).length < 2 ^ (prefixWord ++ tailWord_291952).sum := by decide
  have hdescent : baseEnd_291952 < baseStart_291952 := by decide
  rcases family_descends (prefixWord ++ tailWord_291952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291969 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_291969 : Nat := 118140960795 + 291969 * 2 ^ 59
def prefixEnd_291969 : Nat := 4983230072969 + 3 ^ 40 * 291969 * 2
def baseEnd_291969 : Nat := 149920433212673403644765

theorem tailTrace_291969 : CollatzResearch.WordTrace tailWord_291969 prefixEnd_291969 149920433212673403644765 := by
  unfold tailWord_291969
  simp only [CollatzResearch.WordTrace]
  refine ⟨10648984279253652180406961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7099322852835768120271307 10648984279253652180406961)
  ·
    refine ⟨7986738209440239135305221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10648984279253652180406961 7986738209440239135305221)
    ·
      refine ⟨1497513414270044837869729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7986738209440239135305221 1497513414270044837869729)
      ·
        refine ⟨1123135060702533628402297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1497513414270044837869729 1123135060702533628402297)
        ·
          refine ⟨842351295526900221301723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1123135060702533628402297 842351295526900221301723)
          ·
            refine ⟨1263526943290350331952585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842351295526900221301723 1263526943290350331952585)
            ·
              refine ⟨947645207467762748964439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1263526943290350331952585 947645207467762748964439)
              ·
                refine ⟨1421467811201644123446659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 947645207467762748964439 1421467811201644123446659)
                ·
                  refine ⟨2132201716802466185169989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421467811201644123446659 2132201716802466185169989)
                  ·
                    refine ⟨399787821900462409719373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2132201716802466185169989 399787821900462409719373)
                    ·
                      refine ⟨149920433212673403644765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 399787821900462409719373 149920433212673403644765)
                      ·
                        rfl

theorem cell23_291969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_291969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291969 prefixEnd_291969 := by exact prefixLift 291969
  have htrace : WordTrace (prefixWord ++ tailWord_291969) baseStart_291969 baseEnd_291969 := by
    simpa [prefixWord, tailWord_291969, baseEnd_291969] using wordTrace_append hprefix tailTrace_291969
  have hstable : (prefixWord ++ tailWord_291969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291969).length < 2 ^ (prefixWord ++ tailWord_291969).sum := by decide
  have hdescent : baseEnd_291969 < baseStart_291969 := by decide
  rcases family_descends (prefixWord ++ tailWord_291969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291972 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 8]
def baseStart_291972 : Nat := 118140960795 + 291972 * 2 ^ 59
def prefixEnd_291972 : Nat := 4983230072969 + 3 ^ 40 * 291972 * 2
def baseEnd_291972 : Nat := 16657997072737432434139

theorem tailTrace_291972 : CollatzResearch.WordTrace tailWord_291972 prefixEnd_291972 16657997072737432434139 := by
  unfold tailWord_291972
  simp only [CollatzResearch.WordTrace]
  refine ⟨5324546849121391846383085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7099395798828522461844113 5324546849121391846383085)
  ·
    refine ⟨1996705068420521942393657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5324546849121391846383085 1996705068420521942393657)
    ·
      refine ⟨1497528801315391456795243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1996705068420521942393657 1497528801315391456795243)
      ·
        refine ⟨2246293201973087185192865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1497528801315391456795243 2246293201973087185192865)
        ·
          refine ⟨1684719901479815388894649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2246293201973087185192865 1684719901479815388894649)
          ·
            refine ⟨1263539926109861541670987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1684719901479815388894649 1263539926109861541670987)
            ·
              refine ⟨1895309889164792312506481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263539926109861541670987 1895309889164792312506481)
              ·
                refine ⟨1421482416873594234379861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1895309889164792312506481 1421482416873594234379861)
                ·
                  refine ⟨16657997072737432434139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1421482416873594234379861 16657997072737432434139)
                  ·
                    rfl

theorem cell23_291972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_291972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291972 prefixEnd_291972 := by exact prefixLift 291972
  have htrace : WordTrace (prefixWord ++ tailWord_291972) baseStart_291972 baseEnd_291972 := by
    simpa [prefixWord, tailWord_291972, baseEnd_291972] using wordTrace_append hprefix tailTrace_291972
  have hstable : (prefixWord ++ tailWord_291972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291972).length < 2 ^ (prefixWord ++ tailWord_291972).sum := by decide
  have hdescent : baseEnd_291972 < baseStart_291972 := by decide
  rcases family_descends (prefixWord ++ tailWord_291972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291986 : List Nat := [3, 2, 3, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_291986 : Nat := 118140960795 + 291986 * 2 ^ 59
def prefixEnd_291986 : Nat := 4983230072969 + 3 ^ 40 * 291986 * 2
def baseEnd_291986 : Nat := 149929162383799837132187

theorem tailTrace_291986 : CollatzResearch.WordTrace tailWord_291986 prefixEnd_291986 149929162383799837132187 := by
  unfold tailWord_291986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2662401080048016020943953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7099736213461376055850541 2662401080048016020943953)
  ·
    refine ⟨1996800810036012015707965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2662401080048016020943953 1996800810036012015707965)
    ·
      refine ⟨748800303763504505890487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1996800810036012015707965 748800303763504505890487)
      ·
        refine ⟨1123200455645256758835731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 748800303763504505890487 1123200455645256758835731)
        ·
          refine ⟨1684800683467885138253597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1123200455645256758835731 1684800683467885138253597)
          ·
            refine ⟨631800256300456926845099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1684800683467885138253597 631800256300456926845099)
            ·
              refine ⟨947700384450685390267649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631800256300456926845099 947700384450685390267649)
              ·
                refine ⟨710775288338014042700737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 947700384450685390267649 710775288338014042700737)
                ·
                  refine ⟨533081466253510532025553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 710775288338014042700737 533081466253510532025553)
                  ·
                    refine ⟨399811099690132899019165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 533081466253510532025553 399811099690132899019165)
                    ·
                      refine ⟨149929162383799837132187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 399811099690132899019165 149929162383799837132187)
                      ·
                        rfl

theorem cell23_291986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_291986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_291986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_291986 prefixEnd_291986 := by exact prefixLift 291986
  have htrace : WordTrace (prefixWord ++ tailWord_291986) baseStart_291986 baseEnd_291986 := by
    simpa [prefixWord, tailWord_291986, baseEnd_291986] using wordTrace_append hprefix tailTrace_291986
  have hstable : (prefixWord ++ tailWord_291986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291986).length < 2 ^ (prefixWord ++ tailWord_291986).sum := by decide
  have hdescent : baseEnd_291986 < baseStart_291986 := by decide
  rcases family_descends (prefixWord ++ tailWord_291986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292019 : List Nat := [1, 1, 1, 2, 3, 2, 5, 2, 1, 5]
def baseStart_292019 : Nat := 118140960795 + 292019 * 2 ^ 59
def prefixEnd_292019 : Nat := 4983230072969 + 3 ^ 40 * 292019 * 2
def baseEnd_292019 : Nat := 49982035748466069339845

theorem tailTrace_292019 : CollatzResearch.WordTrace tailWord_292019 prefixEnd_292019 49982035748466069339845 := by
  unfold tailWord_292019
  simp only [CollatzResearch.WordTrace]
  refine ⟨10650807929072510719727111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7100538619381673813151407 10650807929072510719727111)
  ·
    refine ⟨15976211893608766079590667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10650807929072510719727111 15976211893608766079590667)
    ·
      refine ⟨23964317840413149119386001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15976211893608766079590667 23964317840413149119386001)
      ·
        refine ⟨17973238380309861839539501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23964317840413149119386001 17973238380309861839539501)
        ·
          refine ⟨6739964392616198189827313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17973238380309861839539501 6739964392616198189827313)
          ·
            refine ⟨5054973294462148642370485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6739964392616198189827313 5054973294462148642370485)
            ·
              refine ⟨473903746355826435222233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5054973294462148642370485 473903746355826435222233)
              ·
                refine ⟨355427809766869826416675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 473903746355826435222233 355427809766869826416675)
                ·
                  refine ⟨533141714650304739625013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355427809766869826416675 533141714650304739625013)
                  ·
                    refine ⟨49982035748466069339845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 533141714650304739625013 49982035748466069339845)
                    ·
                      rfl

theorem cell23_292019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 5].length) (baseStart_292019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292019 prefixEnd_292019 := by exact prefixLift 292019
  have htrace : WordTrace (prefixWord ++ tailWord_292019) baseStart_292019 baseEnd_292019 := by
    simpa [prefixWord, tailWord_292019, baseEnd_292019] using wordTrace_append hprefix tailTrace_292019
  have hstable : (prefixWord ++ tailWord_292019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292019).length < 2 ^ (prefixWord ++ tailWord_292019).sum := by decide
  have hdescent : baseEnd_292019 < baseStart_292019 := by decide
  rcases family_descends (prefixWord ++ tailWord_292019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292039 : List Nat := [1, 1, 4, 1, 1, 1, 1, 7, 1, 1, 4]
def baseStart_292039 : Nat := 118140960795 + 292039 * 2 ^ 59
def prefixEnd_292039 : Nat := 4983230072969 + 3 ^ 40 * 292039 * 2
def baseEnd_292039 : Nat := 149956376858488129769443

theorem tailTrace_292039 : CollatzResearch.WordTrace tailWord_292039 prefixEnd_292039 149956376858488129769443 := by
  unfold tailWord_292039
  simp only [CollatzResearch.WordTrace]
  refine ⟨10651537389000054135455171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7101024926000036090303447 10651537389000054135455171)
  ·
    refine ⟨15977306083500081203182757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10651537389000054135455171 15977306083500081203182757)
    ·
      refine ⟨2995744890656265225596767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15977306083500081203182757 2995744890656265225596767)
      ·
        refine ⟨4493617335984397838395151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2995744890656265225596767 4493617335984397838395151)
        ·
          refine ⟨6740426003976596757592727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4493617335984397838395151 6740426003976596757592727)
          ·
            refine ⟨10110639005964895136389091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6740426003976596757592727 10110639005964895136389091)
            ·
              refine ⟨15165958508947342704583637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10110639005964895136389091 15165958508947342704583637)
              ·
                refine ⟨355452152553453344638679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15165958508947342704583637 355452152553453344638679)
                ·
                  refine ⟨533178228830180016958019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355452152553453344638679 533178228830180016958019)
                  ·
                    refine ⟨799767343245270025437029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 533178228830180016958019 799767343245270025437029)
                    ·
                      refine ⟨149956376858488129769443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 799767343245270025437029 149956376858488129769443)
                      ·
                        rfl

theorem cell23_292039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_292039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292039 prefixEnd_292039 := by exact prefixLift 292039
  have htrace : WordTrace (prefixWord ++ tailWord_292039) baseStart_292039 baseEnd_292039 := by
    simpa [prefixWord, tailWord_292039, baseEnd_292039] using wordTrace_append hprefix tailTrace_292039
  have hstable : (prefixWord ++ tailWord_292039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292039).length < 2 ^ (prefixWord ++ tailWord_292039).sum := by decide
  have hdescent : baseEnd_292039 < baseStart_292039 := by decide
  rcases family_descends (prefixWord ++ tailWord_292039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292089 : List Nat := [1, 2, 1, 3, 1, 1, 3, 4, 1, 3, 3]
def baseStart_292089 : Nat := 118140960795 + 292089 * 2 ^ 59
def prefixEnd_292089 : Nat := 4983230072969 + 3 ^ 40 * 292089 * 2
def baseEnd_292089 : Nat := 149982050891212934144213

theorem tailTrace_292089 : CollatzResearch.WordTrace tailWord_292089 prefixEnd_292089 149982050891212934144213 := by
  unfold tailWord_292089
  simp only [CollatzResearch.WordTrace]
  refine ⟨10653361038818912674775321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7102240692545941783183547 10653361038818912674775321)
  ·
    refine ⟨7990020779114184506081491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10653361038818912674775321 7990020779114184506081491)
    ·
      refine ⟨11985031168671276759122237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7990020779114184506081491 11985031168671276759122237)
      ·
        refine ⟨4494386688251728784670839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11985031168671276759122237 4494386688251728784670839)
        ·
          refine ⟨6741580032377593177006259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4494386688251728784670839 6741580032377593177006259)
          ·
            refine ⟨10112370048566389765509389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6741580032377593177006259 10112370048566389765509389)
            ·
              refine ⟨3792138768212396162066021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10112370048566389765509389 3792138768212396162066021)
              ·
                refine ⟨711026019039824280387379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3792138768212396162066021 711026019039824280387379)
                ·
                  refine ⟨1066539028559736420581069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711026019039824280387379 1066539028559736420581069)
                  ·
                    refine ⟨399952135709901157717901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1066539028559736420581069 399952135709901157717901)
                    ·
                      refine ⟨149982050891212934144213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 399952135709901157717901 149982050891212934144213)
                      ·
                        rfl

theorem cell23_292089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_292089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292089 prefixEnd_292089 := by exact prefixLift 292089
  have htrace : WordTrace (prefixWord ++ tailWord_292089) baseStart_292089 baseEnd_292089 := by
    simpa [prefixWord, tailWord_292089, baseEnd_292089] using wordTrace_append hprefix tailTrace_292089
  have hstable : (prefixWord ++ tailWord_292089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292089).length < 2 ^ (prefixWord ++ tailWord_292089).sum := by decide
  have hdescent : baseEnd_292089 < baseStart_292089 := by decide
  rcases family_descends (prefixWord ++ tailWord_292089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292090 : List Nat := [3, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2]
def baseStart_292090 : Nat := 118140960795 + 292090 * 2 ^ 59
def prefixEnd_292090 : Nat := 4983230072969 + 3 ^ 40 * 292090 * 2
def baseEnd_292090 : Nat := 149982564371867430231709

theorem tailTrace_292090 : CollatzResearch.WordTrace tailWord_292090 prefixEnd_292090 149982564371867430231709 := by
  unfold tailWord_292090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2663349377953822461390431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7102265007876859897041149 2663349377953822461390431)
  ·
    refine ⟨3995024066930733692085647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2663349377953822461390431 3995024066930733692085647)
    ·
      refine ⟨5992536100396100538128471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3995024066930733692085647 5992536100396100538128471)
      ·
        refine ⟨8988804150594150807192707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5992536100396100538128471 8988804150594150807192707)
        ·
          refine ⟨13483206225891226210789061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8988804150594150807192707 13483206225891226210789061)
          ·
            refine ⟨2528101167354604914522949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13483206225891226210789061 2528101167354604914522949)
            ·
              refine ⟨474018968878988421473053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2528101167354604914522949 474018968878988421473053)
              ·
                refine ⟨177757113329620658052395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 474018968878988421473053 177757113329620658052395)
                ·
                  refine ⟨266635669994430987078593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177757113329620658052395 266635669994430987078593)
                  ·
                    refine ⟨199976752495823240308945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 266635669994430987078593 199976752495823240308945)
                    ·
                      refine ⟨149982564371867430231709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 199976752495823240308945 149982564371867430231709)
                      ·
                        rfl

theorem cell23_292090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2].length) (baseStart_292090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292090 prefixEnd_292090 := by exact prefixLift 292090
  have htrace : WordTrace (prefixWord ++ tailWord_292090) baseStart_292090 baseEnd_292090 := by
    simpa [prefixWord, tailWord_292090, baseEnd_292090] using wordTrace_append hprefix tailTrace_292090
  have hstable : (prefixWord ++ tailWord_292090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292090).length < 2 ^ (prefixWord ++ tailWord_292090).sum := by decide
  have hdescent : baseEnd_292090 < baseStart_292090 := by decide
  rcases family_descends (prefixWord ++ tailWord_292090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292133 : List Nat := [1, 3, 1, 2, 4, 1, 1, 4, 1, 3, 2]
def baseStart_292133 : Nat := 118140960795 + 292133 * 2 ^ 59
def prefixEnd_292133 : Nat := 4983230072969 + 3 ^ 40 * 292133 * 2
def baseEnd_292133 : Nat := 150004644040010761994011

theorem tailTrace_292133 : CollatzResearch.WordTrace tailWord_292133 prefixEnd_292133 150004644040010761994011 := by
  unfold tailWord_292133
  simp only [CollatzResearch.WordTrace]
  refine ⟨10654965850659508189377053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7103310567106338792918035 10654965850659508189377053)
  ·
    refine ⟨3995612193997315571016395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10654965850659508189377053 3995612193997315571016395)
    ·
      refine ⟨5993418290995973356524593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3995612193997315571016395 5993418290995973356524593)
      ·
        refine ⟨4495063718246980017393445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5993418290995973356524593 4495063718246980017393445)
        ·
          refine ⟨842824447171308753261271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4495063718246980017393445 842824447171308753261271)
          ·
            refine ⟨1264236670756963129891907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842824447171308753261271 1264236670756963129891907)
            ·
              refine ⟨1896355006135444694837861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264236670756963129891907 1896355006135444694837861)
              ·
                refine ⟨355566563650395880282099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1896355006135444694837861 355566563650395880282099)
                ·
                  refine ⟨533349845475593820423149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355566563650395880282099 533349845475593820423149)
                  ·
                    refine ⟨200006192053347682658681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 533349845475593820423149 200006192053347682658681)
                    ·
                      refine ⟨150004644040010761994011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 200006192053347682658681 150004644040010761994011)
                      ·
                        rfl

theorem cell23_292133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_292133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292133 prefixEnd_292133 := by exact prefixLift 292133
  have htrace : WordTrace (prefixWord ++ tailWord_292133) baseStart_292133 baseEnd_292133 := by
    simpa [prefixWord, tailWord_292133, baseEnd_292133] using wordTrace_append hprefix tailTrace_292133
  have hstable : (prefixWord ++ tailWord_292133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292133).length < 2 ^ (prefixWord ++ tailWord_292133).sum := by decide
  have hdescent : baseEnd_292133 < baseStart_292133 := by decide
  rcases family_descends (prefixWord ++ tailWord_292133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292149 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_292149 : Nat := 118140960795 + 292149 * 2 ^ 59
def prefixEnd_292149 : Nat := 4983230072969 + 3 ^ 40 * 292149 * 2
def baseEnd_292149 : Nat := 150012859730482699393937

theorem tailTrace_292149 : CollatzResearch.WordTrace tailWord_292149 prefixEnd_292149 150012859730482699393937 := by
  unfold tailWord_292149
  simp only [CollatzResearch.WordTrace]
  refine ⟨10655549418601542921959501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7103699612401028614639667 10655549418601542921959501)
  ·
    refine ⟨3995831031975578595734813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10655549418601542921959501 3995831031975578595734813)
    ·
      refine ⟨1498436636990841973400555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3995831031975578595734813 1498436636990841973400555)
      ·
        refine ⟨2247654955486262960100833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1498436636990841973400555 2247654955486262960100833)
        ·
          refine ⟨1685741216614697220075625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2247654955486262960100833 1685741216614697220075625)
          ·
            refine ⟨1264305912461022915056719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1685741216614697220075625 1264305912461022915056719)
            ·
              refine ⟨1896458868691534372585079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264305912461022915056719 1896458868691534372585079)
              ·
                refine ⟨2844688303037301558877619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1896458868691534372585079 2844688303037301558877619)
                ·
                  refine ⟨4267032454555952338316429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844688303037301558877619 4267032454555952338316429)
                  ·
                    refine ⟨1600137170458482126868661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4267032454555952338316429 1600137170458482126868661)
                    ·
                      refine ⟨150012859730482699393937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1600137170458482126868661 150012859730482699393937)
                      ·
                        rfl

theorem cell23_292149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_292149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292149 prefixEnd_292149 := by exact prefixLift 292149
  have htrace : WordTrace (prefixWord ++ tailWord_292149) baseStart_292149 baseEnd_292149 := by
    simpa [prefixWord, tailWord_292149, baseEnd_292149] using wordTrace_append hprefix tailTrace_292149
  have hstable : (prefixWord ++ tailWord_292149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292149).length < 2 ^ (prefixWord ++ tailWord_292149).sum := by decide
  have hdescent : baseEnd_292149 < baseStart_292149 := by decide
  rcases family_descends (prefixWord ++ tailWord_292149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292163 : List Nat := [1, 1, 1, 3, 1, 3, 1, 6, 2, 2, 2]
def baseStart_292163 : Nat := 118140960795 + 292163 * 2 ^ 59
def prefixEnd_292163 : Nat := 4983230072969 + 3 ^ 40 * 292163 * 2
def baseEnd_292163 : Nat := 150020048459645644618873

theorem tailTrace_292163 : CollatzResearch.WordTrace tailWord_292163 prefixEnd_292163 150020048459645644618873 := by
  unfold tailWord_292163
  simp only [CollatzResearch.WordTrace]
  refine ⟨10656060040550823312969143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7104040027033882208646095 10656060040550823312969143)
  ·
    refine ⟨15984090060826234969453715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10656060040550823312969143 15984090060826234969453715)
    ·
      refine ⟨23976135091239352454180573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15984090060826234969453715 23976135091239352454180573)
      ·
        refine ⟨8991050659214757170317715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23976135091239352454180573 8991050659214757170317715)
        ·
          refine ⟨13486575988822135755476573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8991050659214757170317715 13486575988822135755476573)
          ·
            refine ⟨5057465995808300908303715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13486575988822135755476573 5057465995808300908303715)
            ·
              refine ⟨7586198993712451362455573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5057465995808300908303715 7586198993712451362455573)
              ·
                refine ⟨355603077830271157615105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7586198993712451362455573 355603077830271157615105)
                ·
                  refine ⟨266702308372703368211329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355603077830271157615105 266702308372703368211329)
                  ·
                    refine ⟨200026731279527526158497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 266702308372703368211329 200026731279527526158497)
                    ·
                      refine ⟨150020048459645644618873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 200026731279527526158497 150020048459645644618873)
                      ·
                        rfl

theorem cell23_292163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 2, 2].length) (baseStart_292163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292163 prefixEnd_292163 := by exact prefixLift 292163
  have htrace : WordTrace (prefixWord ++ tailWord_292163) baseStart_292163 baseEnd_292163 := by
    simpa [prefixWord, tailWord_292163, baseEnd_292163] using wordTrace_append hprefix tailTrace_292163
  have hstable : (prefixWord ++ tailWord_292163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292163).length < 2 ^ (prefixWord ++ tailWord_292163).sum := by decide
  have hdescent : baseEnd_292163 < baseStart_292163 := by decide
  rcases family_descends (prefixWord ++ tailWord_292163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292169 : List Nat := [1, 2, 1, 1, 2, 3, 5, 1, 7]
def baseStart_292169 : Nat := 118140960795 + 292169 * 2 ^ 59
def prefixEnd_292169 : Nat := 4983230072969 + 3 ^ 40 * 292169 * 2
def baseEnd_292169 : Nat := 16669236593730291238205

theorem tailTrace_292169 : CollatzResearch.WordTrace tailWord_292169 prefixEnd_292169 16669236593730291238205 := by
  unfold tailWord_292169
  simp only [CollatzResearch.WordTrace]
  refine ⟨10656278878529086337687561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7104185919019390891791707 10656278878529086337687561)
  ·
    refine ⟨7992209158896814753265671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10656278878529086337687561 7992209158896814753265671)
    ·
      refine ⟨11988313738345222129898507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7992209158896814753265671 11988313738345222129898507)
      ·
        refine ⟨17982470607517833194847761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11988313738345222129898507 17982470607517833194847761)
        ·
          refine ⟨13486852955638374896135821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17982470607517833194847761 13486852955638374896135821)
          ·
            refine ⟨5057569858364390586050933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13486852955638374896135821 5057569858364390586050933)
            ·
              refine ⟨474147174221661617442275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5057569858364390586050933 474147174221661617442275)
              ·
                refine ⟨711220761332492426163413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474147174221661617442275 711220761332492426163413)
                ·
                  refine ⟨16669236593730291238205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 711220761332492426163413 16669236593730291238205)
                  ·
                    rfl

theorem cell23_292169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 7].length) (baseStart_292169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292169 prefixEnd_292169 := by exact prefixLift 292169
  have htrace : WordTrace (prefixWord ++ tailWord_292169) baseStart_292169 baseEnd_292169 := by
    simpa [prefixWord, tailWord_292169, baseEnd_292169] using wordTrace_append hprefix tailTrace_292169
  have hstable : (prefixWord ++ tailWord_292169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292169).length < 2 ^ (prefixWord ++ tailWord_292169).sum := by decide
  have hdescent : baseEnd_292169 < baseStart_292169 := by decide
  rcases family_descends (prefixWord ++ tailWord_292169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292179 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 3]
def baseStart_292179 : Nat := 118140960795 + 292179 * 2 ^ 59
def prefixEnd_292179 : Nat := 4983230072969 + 3 ^ 40 * 292179 * 2
def baseEnd_292179 : Nat := 150028264150117582018799

theorem tailTrace_292179 : CollatzResearch.WordTrace tailWord_292179 prefixEnd_292179 150028264150117582018799 := by
  unfold tailWord_292179
  simp only [CollatzResearch.WordTrace]
  refine ⟨10656643608492858045551591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7104429072328572030367727 10656643608492858045551591)
  ·
    refine ⟨15984965412739287068327387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10656643608492858045551591 15984965412739287068327387)
    ·
      refine ⟨23977448119108930602491081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15984965412739287068327387 23977448119108930602491081)
      ·
        refine ⟨17983086089331697951868311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23977448119108930602491081 17983086089331697951868311)
        ·
          refine ⟨26974629133997546927802467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17983086089331697951868311 26974629133997546927802467)
          ·
            refine ⟨40461943700996320391703701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26974629133997546927802467 40461943700996320391703701)
            ·
              refine ⟨1896653610984202518361111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40461943700996320391703701 1896653610984202518361111)
              ·
                refine ⟨2844980416476303777541667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1896653610984202518361111 2844980416476303777541667)
                ·
                  refine ⟨4267470624714455666312501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844980416476303777541667 4267470624714455666312501)
                  ·
                    refine ⟨400075371066980218716797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4267470624714455666312501 400075371066980218716797)
                    ·
                      refine ⟨150028264150117582018799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 400075371066980218716797 150028264150117582018799)
                      ·
                        rfl

theorem cell23_292179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 3].length) (baseStart_292179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292179 prefixEnd_292179 := by exact prefixLift 292179
  have htrace : WordTrace (prefixWord ++ tailWord_292179) baseStart_292179 baseEnd_292179 := by
    simpa [prefixWord, tailWord_292179, baseEnd_292179] using wordTrace_append hprefix tailTrace_292179
  have hstable : (prefixWord ++ tailWord_292179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292179).length < 2 ^ (prefixWord ++ tailWord_292179).sum := by decide
  have hdescent : baseEnd_292179 < baseStart_292179 := by decide
  rcases family_descends (prefixWord ++ tailWord_292179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292180 : List Nat := [2, 4, 1, 1, 2, 1, 3, 3, 2, 2, 2]
def baseStart_292180 : Nat := 118140960795 + 292180 * 2 ^ 59
def prefixEnd_292180 : Nat := 4983230072969 + 3 ^ 40 * 292180 * 2
def baseEnd_292180 : Nat := 150028777630772078106295

theorem tailTrace_292180 : CollatzResearch.WordTrace tailWord_292180 prefixEnd_292180 150028777630772078106295 := by
  unfold tailWord_292180
  simp only [CollatzResearch.WordTrace]
  refine ⟨5328340040744617608168997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7104453387659490144225329 5328340040744617608168997)
  ·
    refine ⟨999063757639615801531687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5328340040744617608168997 999063757639615801531687)
    ·
      refine ⟨1498595636459423702297531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 999063757639615801531687 1498595636459423702297531)
      ·
        refine ⟨2247893454689135553446297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1498595636459423702297531 2247893454689135553446297)
        ·
          refine ⟨1685920091016851665084723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2247893454689135553446297 1685920091016851665084723)
          ·
            refine ⟨2528880136525277497627085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1685920091016851665084723 2528880136525277497627085)
            ·
              refine ⟨948330051196979061610157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2528880136525277497627085 948330051196979061610157)
              ·
                refine ⟨355623769198867148103809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 948330051196979061610157 355623769198867148103809)
                ·
                  refine ⟨266717826899150361077857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355623769198867148103809 266717826899150361077857)
                  ·
                    refine ⟨200038370174362770808393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 266717826899150361077857 200038370174362770808393)
                    ·
                      refine ⟨150028777630772078106295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 200038370174362770808393 150028777630772078106295)
                      ·
                        rfl

theorem cell23_292180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_292180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292180 prefixEnd_292180 := by exact prefixLift 292180
  have htrace : WordTrace (prefixWord ++ tailWord_292180) baseStart_292180 baseEnd_292180 := by
    simpa [prefixWord, tailWord_292180, baseEnd_292180] using wordTrace_append hprefix tailTrace_292180
  have hstable : (prefixWord ++ tailWord_292180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292180).length < 2 ^ (prefixWord ++ tailWord_292180).sum := by decide
  have hdescent : baseEnd_292180 < baseStart_292180 := by decide
  rcases family_descends (prefixWord ++ tailWord_292180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292209 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 1, 2, 5]
def baseStart_292209 : Nat := 118140960795 + 292209 * 2 ^ 59
def prefixEnd_292209 : Nat := 4983230072969 + 3 ^ 40 * 292209 * 2
def baseEnd_292209 : Nat := 150043668569752464643661

theorem tailTrace_292209 : CollatzResearch.WordTrace tailWord_292209 prefixEnd_292209 150043668569752464643661 := by
  unfold tailWord_292209
  simp only [CollatzResearch.WordTrace]
  refine ⟨10657737798384173169143681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7105158532256115446095787 10657737798384173169143681)
  ·
    refine ⟨7993303348788129876857761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10657737798384173169143681 7993303348788129876857761)
    ·
      refine ⟨5994977511591097407643321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7993303348788129876857761 5994977511591097407643321)
      ·
        refine ⟨4496233133693323055732491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5994977511591097407643321 4496233133693323055732491)
        ·
          refine ⟨6744349700539984583598737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4496233133693323055732491 6744349700539984583598737)
          ·
            refine ⟨5058262275404988437699053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6744349700539984583598737 5058262275404988437699053)
            ·
              refine ⟨1896848353276870664137145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5058262275404988437699053 1896848353276870664137145)
              ·
                refine ⟨1422636264957652998102859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1896848353276870664137145 1422636264957652998102859)
                ·
                  refine ⟨2133954397436479497154289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1422636264957652998102859 2133954397436479497154289)
                  ·
                    refine ⟨1600465798077359622865717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2133954397436479497154289 1600465798077359622865717)
                    ·
                      refine ⟨150043668569752464643661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1600465798077359622865717 150043668569752464643661)
                      ·
                        rfl

theorem cell23_292209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_292209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292209 prefixEnd_292209 := by exact prefixLift 292209
  have htrace : WordTrace (prefixWord ++ tailWord_292209) baseStart_292209 baseEnd_292209 := by
    simpa [prefixWord, tailWord_292209, baseEnd_292209] using wordTrace_append hprefix tailTrace_292209
  have hstable : (prefixWord ++ tailWord_292209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292209).length < 2 ^ (prefixWord ++ tailWord_292209).sum := by decide
  have hdescent : baseEnd_292209 < baseStart_292209 := by decide
  rcases family_descends (prefixWord ++ tailWord_292209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292253 : List Nat := [1, 4, 2, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_292253 : Nat := 118140960795 + 292253 * 2 ^ 59
def prefixEnd_292253 : Nat := 4983230072969 + 3 ^ 40 * 292253 * 2
def baseEnd_292253 : Nat := 150066261718550292493459

theorem tailTrace_292253 : CollatzResearch.WordTrace tailWord_292253 prefixEnd_292253 150066261718550292493459 := by
  unfold tailWord_292253
  simp only [CollatzResearch.WordTrace]
  refine ⟨10659342610224768683745413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7106228406816512455830275 10659342610224768683745413)
  ·
    refine ⟨1998626739417144128202265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10659342610224768683745413 1998626739417144128202265)
    ·
      refine ⟨1498970054562858096151699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1998626739417144128202265 1498970054562858096151699)
      ·
        refine ⟨2248455081844287144227549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1498970054562858096151699 2248455081844287144227549)
        ·
          refine ⟨843170655691607679085331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2248455081844287144227549 843170655691607679085331)
          ·
            refine ⟨1264755983537411518627997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843170655691607679085331 1264755983537411518627997)
            ·
              refine ⟨474283493826529319485499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1264755983537411518627997 474283493826529319485499)
              ·
                refine ⟨711425240739793979228249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474283493826529319485499 711425240739793979228249)
                ·
                  refine ⟨533568930554845484421187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 711425240739793979228249 533568930554845484421187)
                  ·
                    refine ⟨800353395832268226631781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 533568930554845484421187 800353395832268226631781)
                    ·
                      refine ⟨150066261718550292493459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 800353395832268226631781 150066261718550292493459)
                      ·
                        rfl

theorem cell23_292253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_292253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292253 prefixEnd_292253 := by exact prefixLift 292253
  have htrace : WordTrace (prefixWord ++ tailWord_292253) baseStart_292253 baseEnd_292253 := by
    simpa [prefixWord, tailWord_292253, baseEnd_292253] using wordTrace_append hprefix tailTrace_292253
  have hstable : (prefixWord ++ tailWord_292253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292253).length < 2 ^ (prefixWord ++ tailWord_292253).sum := by decide
  have hdescent : baseEnd_292253 < baseStart_292253 := by decide
  rcases family_descends (prefixWord ++ tailWord_292253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292256 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 3]
def baseStart_292256 : Nat := 118140960795 + 292256 * 2 ^ 59
def prefixEnd_292256 : Nat := 4983230072969 + 3 ^ 40 * 292256 * 2
def baseEnd_292256 : Nat := 150067802160513780755945

theorem tailTrace_292256 : CollatzResearch.WordTrace tailWord_292256 prefixEnd_292256 150067802160513780755945 := by
  unfold tailWord_292256
  simp only [CollatzResearch.WordTrace]
  refine ⟨5329726014606950098052311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7106301352809266797403081 5329726014606950098052311)
  ·
    refine ⟨7994589021910425147078467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5329726014606950098052311 7994589021910425147078467)
    ·
      refine ⟨11991883532865637720617701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7994589021910425147078467 11991883532865637720617701)
      ·
        refine ⟨2248478162412307072615819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11991883532865637720617701 2248478162412307072615819)
        ·
          refine ⟨3372717243618460608923729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2248478162412307072615819 3372717243618460608923729)
          ·
            refine ⟨2529537932713845456692797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3372717243618460608923729 2529537932713845456692797)
            ·
              refine ⟨948576724767692046259799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2529537932713845456692797 948576724767692046259799)
              ·
                refine ⟨1422865087151538069389699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 948576724767692046259799 1422865087151538069389699)
                ·
                  refine ⟨2134297630727307104084549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1422865087151538069389699 2134297630727307104084549)
                  ·
                    refine ⟨400180805761370082015853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2134297630727307104084549 400180805761370082015853)
                    ·
                      refine ⟨150067802160513780755945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 400180805761370082015853 150067802160513780755945)
                      ·
                        rfl

theorem cell23_292256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_292256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292256 prefixEnd_292256 := by exact prefixLift 292256
  have htrace : WordTrace (prefixWord ++ tailWord_292256) baseStart_292256 baseEnd_292256 := by
    simpa [prefixWord, tailWord_292256, baseEnd_292256] using wordTrace_append hprefix tailTrace_292256
  have hstable : (prefixWord ++ tailWord_292256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292256).length < 2 ^ (prefixWord ++ tailWord_292256).sum := by decide
  have hdescent : baseEnd_292256 < baseStart_292256 := by decide
  rcases family_descends (prefixWord ++ tailWord_292256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292259 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 8]
def baseStart_292259 : Nat := 118140960795 + 292259 * 2 ^ 59
def prefixEnd_292259 : Nat := 4983230072969 + 3 ^ 40 * 292259 * 2
def baseEnd_292259 : Nat := 16674371400275252113159

theorem tailTrace_292259 : CollatzResearch.WordTrace tailWord_292259 prefixEnd_292259 16674371400275252113159 := by
  unfold tailWord_292259
  simp only [CollatzResearch.WordTrace]
  refine ⟨10659561448203031708463831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7106374298802021138975887 10659561448203031708463831)
  ·
    refine ⟨15989342172304547562695747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10659561448203031708463831 15989342172304547562695747)
    ·
      refine ⟨23984013258456821344043621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15989342172304547562695747 23984013258456821344043621)
      ·
        refine ⟨4497002485960654002008179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23984013258456821344043621 4497002485960654002008179)
        ·
          refine ⟨6745503728940981003012269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4497002485960654002008179 6745503728940981003012269)
          ·
            refine ⟨2529563898352867876129601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6745503728940981003012269 2529563898352867876129601)
            ·
              refine ⟨1897172923764650907097201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2529563898352867876129601 1897172923764650907097201)
              ·
                refine ⟨1422879692823488180322901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1897172923764650907097201 1422879692823488180322901)
                ·
                  refine ⟨16674371400275252113159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1422879692823488180322901 16674371400275252113159)
                  ·
                    rfl

theorem cell23_292259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 8].length) (baseStart_292259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292259 prefixEnd_292259 := by exact prefixLift 292259
  have htrace : WordTrace (prefixWord ++ tailWord_292259) baseStart_292259 baseEnd_292259 := by
    simpa [prefixWord, tailWord_292259, baseEnd_292259] using wordTrace_append hprefix tailTrace_292259
  have hstable : (prefixWord ++ tailWord_292259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292259).length < 2 ^ (prefixWord ++ tailWord_292259).sum := by decide
  have hdescent : baseEnd_292259 < baseStart_292259 := by decide
  rcases family_descends (prefixWord ++ tailWord_292259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292279 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 8]
def baseStart_292279 : Nat := 118140960795 + 292279 * 2 ^ 59
def prefixEnd_292279 : Nat := 4983230072969 + 3 ^ 40 * 292279 * 2
def baseEnd_292279 : Nat := 150079612215567190768339

theorem tailTrace_292279 : CollatzResearch.WordTrace tailWord_292279 prefixEnd_292279 150079612215567190768339 := by
  unfold tailWord_292279
  simp only [CollatzResearch.WordTrace]
  refine ⟨10660290908130575124191891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7106860605420383416127927 10660290908130575124191891)
  ·
    refine ⟨15990436362195862686287837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10660290908130575124191891 15990436362195862686287837)
    ·
      refine ⟨5996413635823448507357939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15990436362195862686287837 5996413635823448507357939)
      ·
        refine ⟨8994620453735172761036909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5996413635823448507357939 8994620453735172761036909)
        ·
          refine ⟨3372982670150689785388841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8994620453735172761036909 3372982670150689785388841)
          ·
            refine ⟨2529737002613017339041631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3372982670150689785388841 2529737002613017339041631)
            ·
              refine ⟨3794605503919526008562447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529737002613017339041631 3794605503919526008562447)
              ·
                refine ⟨5691908255879289012843671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3794605503919526008562447 5691908255879289012843671)
                ·
                  refine ⟨8537862383818933519265507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5691908255879289012843671 8537862383818933519265507)
                  ·
                    refine ⟨12806793575728400278898261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8537862383818933519265507 12806793575728400278898261)
                    ·
                      refine ⟨150079612215567190768339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 12806793575728400278898261 150079612215567190768339)
                      ·
                        rfl

theorem cell23_292279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_292279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292279 prefixEnd_292279 := by exact prefixLift 292279
  have htrace : WordTrace (prefixWord ++ tailWord_292279) baseStart_292279 baseEnd_292279 := by
    simpa [prefixWord, tailWord_292279, baseEnd_292279] using wordTrace_append hprefix tailTrace_292279
  have hstable : (prefixWord ++ tailWord_292279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292279).length < 2 ^ (prefixWord ++ tailWord_292279).sum := by decide
  have hdescent : baseEnd_292279 < baseStart_292279 := by decide
  rcases family_descends (prefixWord ++ tailWord_292279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292299 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 7]
def baseStart_292299 : Nat := 118140960795 + 292299 * 2 ^ 59
def prefixEnd_292299 : Nat := 4983230072969 + 3 ^ 40 * 292299 * 2
def baseEnd_292299 : Nat := 150089881828657112518247

theorem tailTrace_292299 : CollatzResearch.WordTrace tailWord_292299 prefixEnd_292299 150089881828657112518247 := by
  unfold tailWord_292299
  simp only [CollatzResearch.WordTrace]
  refine ⟨10661020368058118539919951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7107346912038745693279967 10661020368058118539919951)
  ·
    refine ⟨15991530552087177809879927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10661020368058118539919951 15991530552087177809879927)
    ·
      refine ⟨23987295828130766714819891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15991530552087177809879927 23987295828130766714819891)
      ·
        refine ⟨35980943742196150072229837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23987295828130766714819891 35980943742196150072229837)
        ·
          refine ⟨13492853903323556277086189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35980943742196150072229837 13492853903323556277086189)
          ·
            refine ⟨5059820213746333603907321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13492853903323556277086189 5059820213746333603907321)
            ·
              refine ⟨3794865160309750202930491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5059820213746333603907321 3794865160309750202930491)
              ·
                refine ⟨5692297740464625304395737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3794865160309750202930491 5692297740464625304395737)
                ·
                  refine ⟨4269223305348468978296803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5692297740464625304395737 4269223305348468978296803)
                  ·
                    refine ⟨6403834958022703467445205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4269223305348468978296803 6403834958022703467445205)
                    ·
                      refine ⟨150089881828657112518247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6403834958022703467445205 150089881828657112518247)
                      ·
                        rfl

theorem cell23_292299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 7].length) (baseStart_292299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292299 prefixEnd_292299 := by exact prefixLift 292299
  have htrace : WordTrace (prefixWord ++ tailWord_292299) baseStart_292299 baseEnd_292299 := by
    simpa [prefixWord, tailWord_292299, baseEnd_292299] using wordTrace_append hprefix tailTrace_292299
  have hstable : (prefixWord ++ tailWord_292299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292299).length < 2 ^ (prefixWord ++ tailWord_292299).sum := by decide
  have hdescent : baseEnd_292299 < baseStart_292299 := by decide
  rcases family_descends (prefixWord ++ tailWord_292299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292303 : List Nat := [1, 1, 2, 1, 1, 4, 4, 2, 3, 1, 3]
def baseStart_292303 : Nat := 118140960795 + 292303 * 2 ^ 59
def prefixEnd_292303 : Nat := 4983230072969 + 3 ^ 40 * 292303 * 2
def baseEnd_292303 : Nat := 150091935751275096868229

theorem tailTrace_292303 : CollatzResearch.WordTrace tailWord_292303 prefixEnd_292303 150091935751275096868229 := by
  unfold tailWord_292303
  simp only [CollatzResearch.WordTrace]
  refine ⟨10661166260043627223065563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7107444173362418148710375 10661166260043627223065563)
  ·
    refine ⟨15991749390065440834598345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10661166260043627223065563 15991749390065440834598345)
    ·
      refine ⟨11993812042549080625948759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15991749390065440834598345 11993812042549080625948759)
      ·
        refine ⟨17990718063823620938923139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11993812042549080625948759 17990718063823620938923139)
        ·
          refine ⟨26986077095735431408384709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17990718063823620938923139 26986077095735431408384709)
          ·
            refine ⟨5059889455450393389072133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26986077095735431408384709 5059889455450393389072133)
            ·
              refine ⟨948729272896948760451025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5059889455450393389072133 948729272896948760451025)
              ·
                refine ⟨711546954672711570338269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 948729272896948760451025 711546954672711570338269)
                ·
                  refine ⟨266830108002266838876851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 711546954672711570338269 266830108002266838876851)
                  ·
                    refine ⟨400245162003400258315277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 266830108002266838876851 400245162003400258315277)
                    ·
                      refine ⟨150091935751275096868229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 400245162003400258315277 150091935751275096868229)
                      ·
                        rfl

theorem cell23_292303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 1, 3].length) (baseStart_292303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292303 prefixEnd_292303 := by exact prefixLift 292303
  have htrace : WordTrace (prefixWord ++ tailWord_292303) baseStart_292303 baseEnd_292303 := by
    simpa [prefixWord, tailWord_292303, baseEnd_292303] using wordTrace_append hprefix tailTrace_292303
  have hstable : (prefixWord ++ tailWord_292303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292303).length < 2 ^ (prefixWord ++ tailWord_292303).sum := by decide
  have hdescent : baseEnd_292303 < baseStart_292303 := by decide
  rcases family_descends (prefixWord ++ tailWord_292303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292313 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 1, 5, 2]
def baseStart_292313 : Nat := 118140960795 + 292313 * 2 ^ 59
def prefixEnd_292313 : Nat := 4983230072969 + 3 ^ 40 * 292313 * 2
def baseEnd_292313 : Nat := 150097070557820057743183

theorem tailTrace_292313 : CollatzResearch.WordTrace tailWord_292313 prefixEnd_292313 150097070557820057743183 := by
  unfold tailWord_292313
  simp only [CollatzResearch.WordTrace]
  refine ⟨10661530990007398930929593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7107687326671599287286395 10661530990007398930929593)
  ·
    refine ⟨7996148242505549198197195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10661530990007398930929593 7996148242505549198197195)
    ·
      refine ⟨11994222363758323797295793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7996148242505549198197195 11994222363758323797295793)
      ·
        refine ⟨8995666772818742847971845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11994222363758323797295793 8995666772818742847971845)
        ·
          refine ⟨1686687519903514283994721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8995666772818742847971845 1686687519903514283994721)
          ·
            refine ⟨1265015639927635712996041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1686687519903514283994721 1265015639927635712996041)
            ·
              refine ⟨948761729945726784747031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1265015639927635712996041 948761729945726784747031)
              ·
                refine ⟨1423142594918590177120547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 948761729945726784747031 1423142594918590177120547)
                ·
                  refine ⟨2134713892377885265680821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1423142594918590177120547 2134713892377885265680821)
                  ·
                    refine ⟨200129427410426743657577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2134713892377885265680821 200129427410426743657577)
                    ·
                      refine ⟨150097070557820057743183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 200129427410426743657577 150097070557820057743183)
                      ·
                        rfl

theorem cell23_292313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 5, 2].length) (baseStart_292313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292313 prefixEnd_292313 := by exact prefixLift 292313
  have htrace : WordTrace (prefixWord ++ tailWord_292313) baseStart_292313 baseEnd_292313 := by
    simpa [prefixWord, tailWord_292313, baseEnd_292313] using wordTrace_append hprefix tailTrace_292313
  have hstable : (prefixWord ++ tailWord_292313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292313).length < 2 ^ (prefixWord ++ tailWord_292313).sum := by decide
  have hdescent : baseEnd_292313 < baseStart_292313 := by decide
  rcases family_descends (prefixWord ++ tailWord_292313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292320 : List Nat := [2, 1, 1, 3, 1, 1, 2, 7, 1, 1, 3]
def baseStart_292320 : Nat := 118140960795 + 292320 * 2 ^ 59
def prefixEnd_292320 : Nat := 4983230072969 + 3 ^ 40 * 292320 * 2
def baseEnd_292320 : Nat := 150100664922401530355651

theorem tailTrace_292320 : CollatzResearch.WordTrace tailWord_292320 prefixEnd_292320 150100664922401530355651 := by
  unfold tailWord_292320
  simp only [CollatzResearch.WordTrace]
  refine ⟨5330893150491019563217207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7107857533988026084289609 5330893150491019563217207)
  ·
    refine ⟨7996339725736529344825811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5330893150491019563217207 7996339725736529344825811)
    ·
      refine ⟨11994509588604794017238717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7996339725736529344825811 11994509588604794017238717)
      ·
        refine ⟨4497941095726797756464519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11994509588604794017238717 4497941095726797756464519)
        ·
          refine ⟨6746911643590196634696779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4497941095726797756464519 6746911643590196634696779)
          ·
            refine ⟨10120367465385294952045169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6746911643590196634696779 10120367465385294952045169)
            ·
              refine ⟨7590275599038971214033877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10120367465385294952045169 7590275599038971214033877)
              ·
                refine ⟨177897084352475887828919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7590275599038971214033877 177897084352475887828919)
                ·
                  refine ⟨266845626528713831743379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177897084352475887828919 266845626528713831743379)
                  ·
                    refine ⟨400268439793070747615069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 266845626528713831743379 400268439793070747615069)
                    ·
                      refine ⟨150100664922401530355651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 400268439793070747615069 150100664922401530355651)
                      ·
                        rfl

theorem cell23_292320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_292320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292320 prefixEnd_292320 := by exact prefixLift 292320
  have htrace : WordTrace (prefixWord ++ tailWord_292320) baseStart_292320 baseEnd_292320 := by
    simpa [prefixWord, tailWord_292320, baseEnd_292320] using wordTrace_append hprefix tailTrace_292320
  have hstable : (prefixWord ++ tailWord_292320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292320).length < 2 ^ (prefixWord ++ tailWord_292320).sum := by decide
  have hdescent : baseEnd_292320 < baseStart_292320 := by decide
  rcases family_descends (prefixWord ++ tailWord_292320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292323 : List Nat := [1, 1, 1, 6, 2, 1, 2, 3, 1, 5]
def baseStart_292323 : Nat := 118140960795 + 292323 * 2 ^ 59
def prefixEnd_292323 : Nat := 4983230072969 + 3 ^ 40 * 292323 * 2
def baseEnd_292323 : Nat := 50034068454788339539379

theorem tailTrace_292323 : CollatzResearch.WordTrace tailWord_292323 prefixEnd_292323 50034068454788339539379 := by
  unfold tailWord_292323
  simp only [CollatzResearch.WordTrace]
  refine ⟨10661895719971170638793623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7107930479980780425862415 10661895719971170638793623)
  ·
    refine ⟨15992843579956755958190435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10661895719971170638793623 15992843579956755958190435)
    ·
      refine ⟨23989265369935133937285653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15992843579956755958190435 23989265369935133937285653)
      ·
        refine ⟨1124496814215709403310265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23989265369935133937285653 1124496814215709403310265)
        ·
          refine ⟨843372610661782052482699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1124496814215709403310265 843372610661782052482699)
          ·
            refine ⟨1265058915992673078724049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843372610661782052482699 1265058915992673078724049)
            ·
              refine ⟨948794186994504809043037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1265058915992673078724049 948794186994504809043037)
              ·
                refine ⟨355797820122939303391139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 948794186994504809043037 355797820122939303391139)
                ·
                  refine ⟨533696730184408955086709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355797820122939303391139 533696730184408955086709)
                  ·
                    refine ⟨50034068454788339539379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 533696730184408955086709 50034068454788339539379)
                    ·
                      rfl

theorem cell23_292323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 5].length) (baseStart_292323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292323 prefixEnd_292323 := by exact prefixLift 292323
  have htrace : WordTrace (prefixWord ++ tailWord_292323) baseStart_292323 baseEnd_292323 := by
    simpa [prefixWord, tailWord_292323, baseEnd_292323] using wordTrace_append hprefix tailTrace_292323
  have hstable : (prefixWord ++ tailWord_292323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292323).length < 2 ^ (prefixWord ++ tailWord_292323).sum := by decide
  have hdescent : baseEnd_292323 < baseStart_292323 := by decide
  rcases family_descends (prefixWord ++ tailWord_292323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292346 : List Nat := [3, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5]
def baseStart_292346 : Nat := 118140960795 + 292346 * 2 ^ 59
def prefixEnd_292346 : Nat := 4983230072969 + 3 ^ 40 * 292346 * 2
def baseEnd_292346 : Nat := 150114015419418428630531

theorem tailTrace_292346 : CollatzResearch.WordTrace tailWord_292346 prefixEnd_292346 150114015419418428630531 := by
  unfold tailWord_292346
  simp only [CollatzResearch.WordTrace]
  refine ⟨2665683649721961391720223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7108489732591897044587261 2665683649721961391720223)
  ·
    refine ⟨3998525474582942087580335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2665683649721961391720223 3998525474582942087580335)
    ·
      refine ⟨5997788211874413131370503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3998525474582942087580335 5997788211874413131370503)
      ·
        refine ⟨8996682317811619697055755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5997788211874413131370503 8996682317811619697055755)
        ·
          refine ⟨13495023476717429545583633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8996682317811619697055755 13495023476717429545583633)
          ·
            refine ⟨10121267607538072159187725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13495023476717429545583633 10121267607538072159187725)
            ·
              refine ⟨3795475352826777059695397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10121267607538072159187725 3795475352826777059695397)
              ·
                refine ⟨711651628655020698692887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3795475352826777059695397 711651628655020698692887)
                ·
                  refine ⟨1067477442982531048039331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711651628655020698692887 1067477442982531048039331)
                  ·
                    refine ⟨1601216164473796572058997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1067477442982531048039331 1601216164473796572058997)
                    ·
                      refine ⟨150114015419418428630531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1601216164473796572058997 150114015419418428630531)
                      ·
                        rfl

theorem cell23_292346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_292346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292346 prefixEnd_292346 := by exact prefixLift 292346
  have htrace : WordTrace (prefixWord ++ tailWord_292346) baseStart_292346 baseEnd_292346 := by
    simpa [prefixWord, tailWord_292346, baseEnd_292346] using wordTrace_append hprefix tailTrace_292346
  have hstable : (prefixWord ++ tailWord_292346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292346).length < 2 ^ (prefixWord ++ tailWord_292346).sum := by decide
  have hdescent : baseEnd_292346 < baseStart_292346 := by decide
  rcases family_descends (prefixWord ++ tailWord_292346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292360 : List Nat := [2, 1, 3, 2, 1, 1, 2, 4, 3, 2, 2]
def baseStart_292360 : Nat := 118140960795 + 292360 * 2 ^ 59
def prefixEnd_292360 : Nat := 4983230072969 + 3 ^ 40 * 292360 * 2
def baseEnd_292360 : Nat := 150121204148581373855467

theorem tailTrace_292360 : CollatzResearch.WordTrace tailWord_292360 prefixEnd_292360 150121204148581373855467 := by
  unfold tailWord_292360
  simp only [CollatzResearch.WordTrace]
  refine ⟨5331622610418562978945267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7108830147224750638593689 5331622610418562978945267)
  ·
    refine ⟨7997433915627844468417901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5331622610418562978945267 7997433915627844468417901)
    ·
      refine ⟨2999037718360441675656713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7997433915627844468417901 2999037718360441675656713)
      ·
        refine ⟨2249278288770331256742535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2999037718360441675656713 2249278288770331256742535)
        ·
          refine ⟨3373917433155496885113803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2249278288770331256742535 3373917433155496885113803)
          ·
            refine ⟨5060876149733245327670705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3373917433155496885113803 5060876149733245327670705)
            ·
              refine ⟨3795657112299933995753029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5060876149733245327670705 3795657112299933995753029)
              ·
                refine ⟨711685708556237624203693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3795657112299933995753029 711685708556237624203693)
                ·
                  refine ⟨266882140708589109076385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 711685708556237624203693 266882140708589109076385)
                  ·
                    refine ⟨200161605531441831807289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 266882140708589109076385 200161605531441831807289)
                    ·
                      refine ⟨150121204148581373855467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 200161605531441831807289 150121204148581373855467)
                      ·
                        rfl

theorem cell23_292360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_292360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292360 prefixEnd_292360 := by exact prefixLift 292360
  have htrace : WordTrace (prefixWord ++ tailWord_292360) baseStart_292360 baseEnd_292360 := by
    simpa [prefixWord, tailWord_292360, baseEnd_292360] using wordTrace_append hprefix tailTrace_292360
  have hstable : (prefixWord ++ tailWord_292360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292360).length < 2 ^ (prefixWord ++ tailWord_292360).sum := by decide
  have hdescent : baseEnd_292360 < baseStart_292360 := by decide
  rcases family_descends (prefixWord ++ tailWord_292360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292373 : List Nat := [1, 3, 2, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_292373 : Nat := 118140960795 + 292373 * 2 ^ 59
def prefixEnd_292373 : Nat := 4983230072969 + 3 ^ 40 * 292373 * 2
def baseEnd_292373 : Nat := 150127879397089822992907

theorem tailTrace_292373 : CollatzResearch.WordTrace tailWord_292373 prefixEnd_292373 150127879397089822992907 := by
  unfold tailWord_292373
  simp only [CollatzResearch.WordTrace]
  refine ⟨10663719369790029178113773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7109146246526686118742515 10663719369790029178113773)
  ·
    refine ⟨3998894763671260941792665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10663719369790029178113773 3998894763671260941792665)
    ·
      refine ⟨2999171072753445706344499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3998894763671260941792665 2999171072753445706344499)
      ·
        refine ⟨4498756609130168559516749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2999171072753445706344499 4498756609130168559516749)
        ·
          refine ⟨1687033728423813209818781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4498756609130168559516749 1687033728423813209818781)
          ·
            refine ⟨632637648158929953682043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1687033728423813209818781 632637648158929953682043)
            ·
              refine ⟨948956472238394930523065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632637648158929953682043 948956472238394930523065)
              ·
                refine ⟨711717354178796197892299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 948956472238394930523065 711717354178796197892299)
                ·
                  refine ⟨1067576031268194296838449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711717354178796197892299 1067576031268194296838449)
                  ·
                    refine ⟨800682023451145722628837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1067576031268194296838449 800682023451145722628837)
                    ·
                      refine ⟨150127879397089822992907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 800682023451145722628837 150127879397089822992907)
                      ·
                        rfl

theorem cell23_292373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_292373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292373 prefixEnd_292373 := by exact prefixLift 292373
  have htrace : WordTrace (prefixWord ++ tailWord_292373) baseStart_292373 baseEnd_292373 := by
    simpa [prefixWord, tailWord_292373, baseEnd_292373] using wordTrace_append hprefix tailTrace_292373
  have hstable : (prefixWord ++ tailWord_292373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292373).length < 2 ^ (prefixWord ++ tailWord_292373).sum := by decide
  have hdescent : baseEnd_292373 < baseStart_292373 := by decide
  rcases family_descends (prefixWord ++ tailWord_292373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292394 : List Nat := [3, 1, 4, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_292394 : Nat := 118140960795 + 292394 * 2 ^ 59
def prefixEnd_292394 : Nat := 4983230072969 + 3 ^ 40 * 292394 * 2
def baseEnd_292394 : Nat := 150138662490834240830311

theorem tailTrace_292394 : CollatzResearch.WordTrace tailWord_292394 prefixEnd_292394 150138662490834240830311 := by
  unfold tailWord_292394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2666121325678487441157059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7109656868475966509752157 2666121325678487441157059)
  ·
    refine ⟨3999181988517731161735589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2666121325678487441157059 3999181988517731161735589)
    ·
      refine ⟨749846622847074592825423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3999181988517731161735589 749846622847074592825423)
      ·
        refine ⟨1124769934270611889238135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749846622847074592825423 1124769934270611889238135)
        ·
          refine ⟨1687154901405917833857203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124769934270611889238135 1687154901405917833857203)
          ·
            refine ⟨2530732352108876750785805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1687154901405917833857203 2530732352108876750785805)
            ·
              refine ⟨949024632040828781544677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2530732352108876750785805 949024632040828781544677)
              ·
                refine ⟨177942118507655396539627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 949024632040828781544677 177942118507655396539627)
                ·
                  refine ⟨266913177761483094809441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177942118507655396539627 266913177761483094809441)
                  ·
                    refine ⟨200184883321112321107081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 266913177761483094809441 200184883321112321107081)
                    ·
                      refine ⟨150138662490834240830311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 200184883321112321107081 150138662490834240830311)
                      ·
                        rfl

theorem cell23_292394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_292394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292394 prefixEnd_292394 := by exact prefixLift 292394
  have htrace : WordTrace (prefixWord ++ tailWord_292394) baseStart_292394 baseEnd_292394 := by
    simpa [prefixWord, tailWord_292394, baseEnd_292394] using wordTrace_append hprefix tailTrace_292394
  have hstable : (prefixWord ++ tailWord_292394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292394).length < 2 ^ (prefixWord ++ tailWord_292394).sum := by decide
  have hdescent : baseEnd_292394 < baseStart_292394 := by decide
  rcases family_descends (prefixWord ++ tailWord_292394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292410 : List Nat := [3, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3]
def baseStart_292410 : Nat := 118140960795 + 292410 * 2 ^ 59
def prefixEnd_292410 : Nat := 4983230072969 + 3 ^ 40 * 292410 * 2
def baseEnd_292410 : Nat := 150146878181306178230237

theorem tailTrace_292410 : CollatzResearch.WordTrace tailWord_292410 prefixEnd_292410 150146878181306178230237 := by
  unfold tailWord_292410
  simp only [CollatzResearch.WordTrace]
  refine ⟨2666267217663996124302671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7110045913770656331473789 2666267217663996124302671)
  ·
    refine ⟨3999400826495994186454007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2666267217663996124302671 3999400826495994186454007)
    ·
      refine ⟨5999101239743991279681011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3999400826495994186454007 5999101239743991279681011)
      ·
        refine ⟨8998651859615986919521517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5999101239743991279681011 8998651859615986919521517)
        ·
          refine ⟨3374494447355995094820569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8998651859615986919521517 3374494447355995094820569)
          ·
            refine ⟨2530870835516996321115427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3374494447355995094820569 2530870835516996321115427)
            ·
              refine ⟨3796306253275494481673141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2530870835516996321115427 3796306253275494481673141)
              ·
                refine ⟨355903711244577607656857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3796306253275494481673141 355903711244577607656857)
                ·
                  refine ⟨266927783433433205742643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355903711244577607656857 266927783433433205742643)
                  ·
                    refine ⟨400391675150149808613965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 266927783433433205742643 400391675150149808613965)
                    ·
                      refine ⟨150146878181306178230237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 400391675150149808613965 150146878181306178230237)
                      ·
                        rfl

theorem cell23_292410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3].length) (baseStart_292410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292410 prefixEnd_292410 := by exact prefixLift 292410
  have htrace : WordTrace (prefixWord ++ tailWord_292410) baseStart_292410 baseEnd_292410 := by
    simpa [prefixWord, tailWord_292410, baseEnd_292410] using wordTrace_append hprefix tailTrace_292410
  have hstable : (prefixWord ++ tailWord_292410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292410).length < 2 ^ (prefixWord ++ tailWord_292410).sum := by decide
  have hdescent : baseEnd_292410 < baseStart_292410 := by decide
  rcases family_descends (prefixWord ++ tailWord_292410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292416 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 4]
def baseStart_292416 : Nat := 118140960795 + 292416 * 2 ^ 59
def prefixEnd_292416 : Nat := 4983230072969 + 3 ^ 40 * 292416 * 2
def baseEnd_292416 : Nat := 150149959065233154755209

theorem tailTrace_292416 : CollatzResearch.WordTrace tailWord_292416 prefixEnd_292416 150149959065233154755209 := by
  unfold tailWord_292416
  simp only [CollatzResearch.WordTrace]
  refine ⟨5332643854317123760964551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7110191805756165014619401 5332643854317123760964551)
  ·
    refine ⟨7998965781475685641446827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5332643854317123760964551 7998965781475685641446827)
    ·
      refine ⟨11998448672213528462170241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7998965781475685641446827 11998448672213528462170241)
      ·
        refine ⟨8998836504160146346627681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11998448672213528462170241 8998836504160146346627681)
        ·
          refine ⟨6749127378120109759970761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8998836504160146346627681 6749127378120109759970761)
          ·
            refine ⟨5061845533590082319978071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6749127378120109759970761 5061845533590082319978071)
            ·
              refine ⟨7592768300385123479967107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5061845533590082319978071 7592768300385123479967107)
              ·
                refine ⟨11389152450577685219950661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7592768300385123479967107 11389152450577685219950661)
                ·
                  refine ⟨2135466084483315978740749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11389152450577685219950661 2135466084483315978740749)
                  ·
                    refine ⟨800799781681243492027781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2135466084483315978740749 800799781681243492027781)
                    ·
                      refine ⟨150149959065233154755209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 800799781681243492027781 150149959065233154755209)
                      ·
                        rfl

theorem cell23_292416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_292416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292416 prefixEnd_292416 := by exact prefixLift 292416
  have htrace : WordTrace (prefixWord ++ tailWord_292416) baseStart_292416 baseEnd_292416 := by
    simpa [prefixWord, tailWord_292416, baseEnd_292416] using wordTrace_append hprefix tailTrace_292416
  have hstable : (prefixWord ++ tailWord_292416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292416).length < 2 ^ (prefixWord ++ tailWord_292416).sum := by decide
  have hdescent : baseEnd_292416 < baseStart_292416 := by decide
  rcases family_descends (prefixWord ++ tailWord_292416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292426 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 1, 8]
def baseStart_292426 : Nat := 118140960795 + 292426 * 2 ^ 59
def prefixEnd_292426 : Nat := 4983230072969 + 3 ^ 40 * 292426 * 2
def baseEnd_292426 : Nat := 50051697957259371876721

theorem tailTrace_292426 : CollatzResearch.WordTrace tailWord_292426 prefixEnd_292426 50051697957259371876721 := by
  unfold tailWord_292426
  simp only [CollatzResearch.WordTrace]
  refine ⟨2666413109649504807448283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7110434959065346153195421 2666413109649504807448283)
  ·
    refine ⟨3999619664474257211172425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2666413109649504807448283 3999619664474257211172425)
    ·
      refine ⟨2999714748355692908379319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3999619664474257211172425 2999714748355692908379319)
      ·
        refine ⟨4499572122533539362568979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2999714748355692908379319 4499572122533539362568979)
        ·
          refine ⟨6749358183800309043853469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4499572122533539362568979 6749358183800309043853469)
          ·
            refine ⟨2531009318925115891445051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6749358183800309043853469 2531009318925115891445051)
            ·
              refine ⟨3796513978387673837167577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2531009318925115891445051 3796513978387673837167577)
              ·
                refine ⟨2847385483790755377875683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3796513978387673837167577 2847385483790755377875683)
                ·
                  refine ⟨4271078225686133066813525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2847385483790755377875683 4271078225686133066813525)
                  ·
                    refine ⟨50051697957259371876721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4271078225686133066813525 50051697957259371876721)
                    ·
                      rfl

theorem cell23_292426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_292426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292426 prefixEnd_292426 := by exact prefixLift 292426
  have htrace : WordTrace (prefixWord ++ tailWord_292426) baseStart_292426 baseEnd_292426 := by
    simpa [prefixWord, tailWord_292426, baseEnd_292426] using wordTrace_append hprefix tailTrace_292426
  have hstable : (prefixWord ++ tailWord_292426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292426).length < 2 ^ (prefixWord ++ tailWord_292426).sum := by decide
  have hdescent : baseEnd_292426 < baseStart_292426 := by decide
  rcases family_descends (prefixWord ++ tailWord_292426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292438 : List Nat := [5, 2, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_292438 : Nat := 118140960795 + 292438 * 2 ^ 59
def prefixEnd_292438 : Nat := 4983230072969 + 3 ^ 40 * 292438 * 2
def baseEnd_292438 : Nat := 50053751879877356226703

theorem tailTrace_292438 : CollatzResearch.WordTrace tailWord_292438 prefixEnd_292438 50053751879877356226703 := by
  unfold tailWord_292438
  simp only [CollatzResearch.WordTrace]
  refine ⟨666630632159659079951873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7110726743036363519486645 666630632159659079951873)
  ·
    refine ⟨499972974119744309963905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 666630632159659079951873 499972974119744309963905)
    ·
      refine ⟨374979730589808232472929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 499972974119744309963905 374979730589808232472929)
      ·
        refine ⟨281234797942356174354697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374979730589808232472929 281234797942356174354697)
        ·
          refine ⟨210926098456767130766023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281234797942356174354697 210926098456767130766023)
          ·
            refine ⟨316389147685150696149035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210926098456767130766023 316389147685150696149035)
            ·
              refine ⟨474583721527726044223553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316389147685150696149035 474583721527726044223553)
              ·
                refine ⟨355937791145794533167665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474583721527726044223553 355937791145794533167665)
                ·
                  refine ⟨266953343359345899875749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355937791145794533167665 266953343359345899875749)
                  ·
                    refine ⟨50053751879877356226703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 266953343359345899875749 50053751879877356226703)
                    ·
                      rfl

theorem cell23_292438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_292438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292438 prefixEnd_292438 := by exact prefixLift 292438
  have htrace : WordTrace (prefixWord ++ tailWord_292438) baseStart_292438 baseEnd_292438 := by
    simpa [prefixWord, tailWord_292438, baseEnd_292438] using wordTrace_append hprefix tailTrace_292438
  have hstable : (prefixWord ++ tailWord_292438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292438).length < 2 ^ (prefixWord ++ tailWord_292438).sum := by decide
  have hdescent : baseEnd_292438 < baseStart_292438 := by decide
  rcases family_descends (prefixWord ++ tailWord_292438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292444 : List Nat := [2, 2, 4, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_292444 : Nat := 118140960795 + 292444 * 2 ^ 59
def prefixEnd_292444 : Nat := 4983230072969 + 3 ^ 40 * 292444 * 2
def baseEnd_292444 : Nat := 150164336523559045205081

theorem tailTrace_292444 : CollatzResearch.WordTrace tailWord_292444 prefixEnd_292444 150164336523559045205081 := by
  unfold tailWord_292444
  simp only [CollatzResearch.WordTrace]
  refine ⟨5333154476266404151974193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7110872635021872202632257 5333154476266404151974193)
  ·
    refine ⟨3999865857199803113980645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5333154476266404151974193 3999865857199803113980645)
    ·
      refine ⟨749974848224963083871371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3999865857199803113980645 749974848224963083871371)
      ·
        refine ⟨1124962272337444625807057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749974848224963083871371 1124962272337444625807057)
        ·
          refine ⟨843721704253083469355293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1124962272337444625807057 843721704253083469355293)
          ·
            refine ⟨316395639094906301008235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 843721704253083469355293 316395639094906301008235)
            ·
              refine ⟨474593458642359451512353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316395639094906301008235 474593458642359451512353)
              ·
                refine ⟨355945093981769588634265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474593458642359451512353 355945093981769588634265)
                ·
                  refine ⟨266958820486327191475699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355945093981769588634265 266958820486327191475699)
                  ·
                    refine ⟨400438230729490787213549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 266958820486327191475699 400438230729490787213549)
                    ·
                      refine ⟨150164336523559045205081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 400438230729490787213549 150164336523559045205081)
                      ·
                        rfl

theorem cell23_292444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_292444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292444 prefixEnd_292444 := by exact prefixLift 292444
  have htrace : WordTrace (prefixWord ++ tailWord_292444) baseStart_292444 baseEnd_292444 := by
    simpa [prefixWord, tailWord_292444, baseEnd_292444] using wordTrace_append hprefix tailTrace_292444
  have hstable : (prefixWord ++ tailWord_292444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292444).length < 2 ^ (prefixWord ++ tailWord_292444).sum := by decide
  have hdescent : baseEnd_292444 < baseStart_292444 := by decide
  rcases family_descends (prefixWord ++ tailWord_292444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292496 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 7]
def baseStart_292496 : Nat := 118140960795 + 292496 * 2 ^ 59
def prefixEnd_292496 : Nat := 4983230072969 + 3 ^ 40 * 292496 * 2
def baseEnd_292496 : Nat := 150191037517592841754841

theorem tailTrace_292496 : CollatzResearch.WordTrace tailWord_292496 prefixEnd_292496 150191037517592841754841 := by
  unfold tailWord_292496
  simp only [CollatzResearch.WordTrace]
  refine ⟨5334102774172210592420671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7112137032229614123227561 5334102774172210592420671)
  ·
    refine ⟨8001154161258315888631007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5334102774172210592420671 8001154161258315888631007)
    ·
      refine ⟨12001731241887473832946511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8001154161258315888631007 12001731241887473832946511)
      ·
        refine ⟨18002596862831210749419767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12001731241887473832946511 18002596862831210749419767)
        ·
          refine ⟨27003895294246816124129651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18002596862831210749419767 27003895294246816124129651)
          ·
            refine ⟨40505842941370224186194477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27003895294246816124129651 40505842941370224186194477)
            ·
              refine ⟨15189691103013834069822929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40505842941370224186194477 15189691103013834069822929)
              ·
                refine ⟨11392268327260375552367197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15189691103013834069822929 11392268327260375552367197)
                ·
                  refine ⟨4272100622722640832137699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11392268327260375552367197 4272100622722640832137699)
                  ·
                    refine ⟨6408150934083961248206549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4272100622722640832137699 6408150934083961248206549)
                    ·
                      refine ⟨150191037517592841754841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6408150934083961248206549 150191037517592841754841)
                      ·
                        rfl

theorem cell23_292496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_292496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292496 prefixEnd_292496 := by exact prefixLift 292496
  have htrace : WordTrace (prefixWord ++ tailWord_292496) baseStart_292496 baseEnd_292496 := by
    simpa [prefixWord, tailWord_292496, baseEnd_292496] using wordTrace_append hprefix tailTrace_292496
  have hstable : (prefixWord ++ tailWord_292496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292496).length < 2 ^ (prefixWord ++ tailWord_292496).sum := by decide
  have hdescent : baseEnd_292496 < baseStart_292496 := by decide
  rcases family_descends (prefixWord ++ tailWord_292496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292503 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 4, 5]
def baseStart_292503 : Nat := 118140960795 + 292503 * 2 ^ 59
def prefixEnd_292503 : Nat := 4983230072969 + 3 ^ 40 * 292503 * 2
def baseEnd_292503 : Nat := 50064877294058104789103

theorem tailTrace_292503 : CollatzResearch.WordTrace tailWord_292503 prefixEnd_292503 50064877294058104789103 := by
  unfold tailWord_292503
  simp only [CollatzResearch.WordTrace]
  refine ⟨10668460859319061380346163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7112307239546040920230775 10668460859319061380346163)
  ·
    refine ⟨16002691288978592070519245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10668460859319061380346163 16002691288978592070519245)
    ·
      refine ⟨6001009233366972026444717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16002691288978592070519245 6001009233366972026444717)
      ·
        refine ⟨2250378462512614509916769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6001009233366972026444717 2250378462512614509916769)
        ·
          refine ⟨1687783846884460882437577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2250378462512614509916769 1687783846884460882437577)
          ·
            refine ⟨1265837885163345661828183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1687783846884460882437577 1265837885163345661828183)
            ·
              refine ⟨1898756827745018492742275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265837885163345661828183 1898756827745018492742275)
              ·
                refine ⟨2848135241617527739113413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1898756827745018492742275 2848135241617527739113413)
                ·
                  refine ⟨534025357803286451083765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2848135241617527739113413 534025357803286451083765)
                  ·
                    refine ⟨50064877294058104789103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 534025357803286451083765 50064877294058104789103)
                    ·
                      rfl

theorem cell23_292503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_292503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292503 prefixEnd_292503 := by exact prefixLift 292503
  have htrace : WordTrace (prefixWord ++ tailWord_292503) baseStart_292503 baseEnd_292503 := by
    simpa [prefixWord, tailWord_292503, baseEnd_292503] using wordTrace_append hprefix tailTrace_292503
  have hstable : (prefixWord ++ tailWord_292503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292503).length < 2 ^ (prefixWord ++ tailWord_292503).sum := by decide
  have hdescent : baseEnd_292503 < baseStart_292503 := by decide
  rcases family_descends (prefixWord ++ tailWord_292503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292513 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_292513 : Nat := 118140960795 + 292513 * 2 ^ 59
def prefixEnd_292513 : Nat := 4983230072969 + 3 ^ 40 * 292513 * 2
def baseEnd_292513 : Nat := 150199766688719275242263

theorem tailTrace_292513 : CollatzResearch.WordTrace tailWord_292513 prefixEnd_292513 150199766688719275242263 := by
  unfold tailWord_292513
  simp only [CollatzResearch.WordTrace]
  refine ⟨10668825589282833088210193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7112550392855222058806795 10668825589282833088210193)
  ·
    refine ⟨8001619191962124816157645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10668825589282833088210193 8001619191962124816157645)
    ·
      refine ⟨3000607196985796806059117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8001619191962124816157645 3000607196985796806059117)
      ·
        refine ⟨1125227698869673802272169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3000607196985796806059117 1125227698869673802272169)
        ·
          refine ⟨843920774152255351704127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1125227698869673802272169 843920774152255351704127)
          ·
            refine ⟨1265881161228383027556191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843920774152255351704127 1265881161228383027556191)
            ·
              refine ⟨1898821741842574541334287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265881161228383027556191 1898821741842574541334287)
              ·
                refine ⟨2848232612763861812001431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1898821741842574541334287 2848232612763861812001431)
                ·
                  refine ⟨4272348919145792718002147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2848232612763861812001431 4272348919145792718002147)
                  ·
                    refine ⟨6408523378718689077003221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4272348919145792718002147 6408523378718689077003221)
                    ·
                      refine ⟨150199766688719275242263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6408523378718689077003221 150199766688719275242263)
                      ·
                        rfl

theorem cell23_292513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_292513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292513 prefixEnd_292513 := by exact prefixLift 292513
  have htrace : WordTrace (prefixWord ++ tailWord_292513) baseStart_292513 baseEnd_292513 := by
    simpa [prefixWord, tailWord_292513, baseEnd_292513] using wordTrace_append hprefix tailTrace_292513
  have hstable : (prefixWord ++ tailWord_292513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292513).length < 2 ^ (prefixWord ++ tailWord_292513).sum := by decide
  have hdescent : baseEnd_292513 < baseStart_292513 := by decide
  rcases family_descends (prefixWord ++ tailWord_292513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292540 : List Nat := [2, 2, 2, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_292540 : Nat := 118140960795 + 292540 * 2 ^ 59
def prefixEnd_292540 : Nat := 4983230072969 + 3 ^ 40 * 292540 * 2
def baseEnd_292540 : Nat := 150213630666390669604639

theorem tailTrace_292540 : CollatzResearch.WordTrace tailWord_292540 prefixEnd_292540 150213630666390669604639 := by
  unfold tailWord_292540
  simp only [CollatzResearch.WordTrace]
  refine ⟨5334905180092508349721537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7113206906790011132962049 5334905180092508349721537)
  ·
    refine ⟨4001178885069381262291153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5334905180092508349721537 4001178885069381262291153)
    ·
      refine ⟨3000884163802035946718365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4001178885069381262291153 3000884163802035946718365)
      ·
        refine ⟨1125331561425763480019387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3000884163802035946718365 1125331561425763480019387)
        ·
          refine ⟨1687997342138645220029081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1125331561425763480019387 1687997342138645220029081)
          ·
            refine ⟨1265998006603983915021811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1687997342138645220029081 1265998006603983915021811)
            ·
              refine ⟨1898997009905975872532717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265998006603983915021811 1898997009905975872532717)
              ·
                refine ⟨712123878714740952199769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1898997009905975872532717 712123878714740952199769)
                ·
                  refine ⟨534092909036055714149827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 712123878714740952199769 534092909036055714149827)
                  ·
                    refine ⟨801139363554083571224741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 534092909036055714149827 801139363554083571224741)
                    ·
                      refine ⟨150213630666390669604639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 801139363554083571224741 150213630666390669604639)
                      ·
                        rfl

theorem cell23_292540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_292540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292540 prefixEnd_292540 := by exact prefixLift 292540
  have htrace : WordTrace (prefixWord ++ tailWord_292540) baseStart_292540 baseEnd_292540 := by
    simpa [prefixWord, tailWord_292540, baseEnd_292540] using wordTrace_append hprefix tailTrace_292540
  have hstable : (prefixWord ++ tailWord_292540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292540).length < 2 ^ (prefixWord ++ tailWord_292540).sum := by decide
  have hdescent : baseEnd_292540 < baseStart_292540 := by decide
  rcases family_descends (prefixWord ++ tailWord_292540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292567 : List Nat := [1, 1, 3, 2, 1, 3, 3, 4, 1, 4]
def baseStart_292567 : Nat := 118140960795 + 292567 * 2 ^ 59
def prefixEnd_292567 : Nat := 4983230072969 + 3 ^ 40 * 292567 * 2
def baseEnd_292567 : Nat := 50075831548020687989005

theorem tailTrace_292567 : CollatzResearch.WordTrace tailWord_292567 prefixEnd_292567 50075831548020687989005 := by
  unfold tailWord_292567
  simp only [CollatzResearch.WordTrace]
  refine ⟨10670795131087200310675955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7113863420724800207117303 10670795131087200310675955)
  ·
    refine ⟨16006192696630800466013933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10670795131087200310675955 16006192696630800466013933)
    ·
      refine ⟨6002322261236550174755225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16006192696630800466013933 6002322261236550174755225)
      ·
        refine ⟨4501741695927412631066419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6002322261236550174755225 4501741695927412631066419)
        ·
          refine ⟨6752612543891118946599629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4501741695927412631066419 6752612543891118946599629)
          ·
            refine ⟨2532229703959169604974861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6752612543891118946599629 2532229703959169604974861)
            ·
              refine ⟨949586138984688601865573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2532229703959169604974861 949586138984688601865573)
              ·
                refine ⟨178047401059629112849795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 949586138984688601865573 178047401059629112849795)
                ·
                  refine ⟨267071101589443669274693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178047401059629112849795 267071101589443669274693)
                  ·
                    refine ⟨50075831548020687989005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 267071101589443669274693 50075831548020687989005)
                    ·
                      rfl

theorem cell23_292567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 1, 4].length) (baseStart_292567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292567 prefixEnd_292567 := by exact prefixLift 292567
  have htrace : WordTrace (prefixWord ++ tailWord_292567) baseStart_292567 baseEnd_292567 := by
    simpa [prefixWord, tailWord_292567, baseEnd_292567] using wordTrace_append hprefix tailTrace_292567
  have hstable : (prefixWord ++ tailWord_292567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292567).length < 2 ^ (prefixWord ++ tailWord_292567).sum := by decide
  have hdescent : baseEnd_292567 < baseStart_292567 := by decide
  rcases family_descends (prefixWord ++ tailWord_292567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292670 : List Nat := [4, 2, 1, 2, 2, 1, 11]
def baseStart_292670 : Nat := 118140960795 + 292670 * 2 ^ 59
def prefixEnd_292670 : Nat := 4983230072969 + 3 ^ 40 * 292670 * 2
def baseEnd_292670 : Nat := 1855313372240434086161

theorem tailTrace_292670 : CollatzResearch.WordTrace tailWord_292670 prefixEnd_292670 1855313372240434086161 := by
  unfold tailWord_292670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1334318981214256112709433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7116367899809365934450309 1334318981214256112709433)
  ·
    refine ⟨1000739235910692084532075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1334318981214256112709433 1000739235910692084532075)
    ·
      refine ⟨1501108853866038126798113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1000739235910692084532075 1501108853866038126798113)
      ·
        refine ⟨1125831640399528595098585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1501108853866038126798113 1125831640399528595098585)
        ·
          refine ⟨844373730299646446323939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1125831640399528595098585 844373730299646446323939)
          ·
            refine ⟨1266560595449469669485909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844373730299646446323939 1266560595449469669485909)
            ·
              refine ⟨1855313372240434086161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1266560595449469669485909 1855313372240434086161)
              ·
                rfl

theorem cell23_292670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 11].length) (baseStart_292670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292670 prefixEnd_292670 := by exact prefixLift 292670
  have htrace : WordTrace (prefixWord ++ tailWord_292670) baseStart_292670 baseEnd_292670 := by
    simpa [prefixWord, tailWord_292670, baseEnd_292670] using wordTrace_append hprefix tailTrace_292670
  have hstable : (prefixWord ++ tailWord_292670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292670).length < 2 ^ (prefixWord ++ tailWord_292670).sum := by decide
  have hdescent : baseEnd_292670 < baseStart_292670 := by decide
  rcases family_descends (prefixWord ++ tailWord_292670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292740 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_292740 : Nat := 118140960795 + 292740 * 2 ^ 59
def prefixEnd_292740 : Nat := 4983230072969 + 3 ^ 40 * 292740 * 2
def baseEnd_292740 : Nat := 150316326797289887103719

theorem tailTrace_292740 : CollatzResearch.WordTrace tailWord_292740 prefixEnd_292740 150316326797289887103719 := by
  unfold tailWord_292740
  simp only [CollatzResearch.WordTrace]
  refine ⟨5338552479730225428361837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7118069972973633904482449 5338552479730225428361837)
  ·
    refine ⟨2001957179898834535635689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5338552479730225428361837 2001957179898834535635689)
    ·
      refine ⟨1501467884924125901726767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2001957179898834535635689 1501467884924125901726767)
      ·
        refine ⟨2252201827386188852590151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1501467884924125901726767 2252201827386188852590151)
        ·
          refine ⟨3378302741079283278885227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2252201827386188852590151 3378302741079283278885227)
          ·
            refine ⟨5067454111618924918327841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3378302741079283278885227 5067454111618924918327841)
            ·
              refine ⟨3800590583714193688745881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5067454111618924918327841 3800590583714193688745881)
              ·
                refine ⟨2850442937785645266559411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3800590583714193688745881 2850442937785645266559411)
                ·
                  refine ⟨4275664406678467899839117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2850442937785645266559411 4275664406678467899839117)
                  ·
                    refine ⟨1603374152504425462439669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4275664406678467899839117 1603374152504425462439669)
                    ·
                      refine ⟨150316326797289887103719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1603374152504425462439669 150316326797289887103719)
                      ·
                        rfl

theorem cell23_292740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_292740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292740 prefixEnd_292740 := by exact prefixLift 292740
  have htrace : WordTrace (prefixWord ++ tailWord_292740) baseStart_292740 baseEnd_292740 := by
    simpa [prefixWord, tailWord_292740, baseEnd_292740] using wordTrace_append hprefix tailTrace_292740
  have hstable : (prefixWord ++ tailWord_292740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292740).length < 2 ^ (prefixWord ++ tailWord_292740).sum := by decide
  have hdescent : baseEnd_292740 < baseStart_292740 := by decide
  rcases family_descends (prefixWord ++ tailWord_292740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292782 : List Nat := [4, 1, 5, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_292782 : Nat := 118140960795 + 292782 * 2 ^ 59
def prefixEnd_292782 : Nat := 4983230072969 + 3 ^ 40 * 292782 * 2
def baseEnd_292782 : Nat := 150337892984778722778527

theorem tailTrace_292782 : CollatzResearch.WordTrace tailWord_292782 prefixEnd_292782 150337892984778722778527 := by
  unfold tailWord_292782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1334829603163536503719075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7119091216872194686501733 1334829603163536503719075)
  ·
    refine ⟨2002244404745304755578613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1334829603163536503719075 2002244404745304755578613)
    ·
      refine ⟨187710412944872320835495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2002244404745304755578613 187710412944872320835495)
      ·
        refine ⟨281565619417308481253243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187710412944872320835495 281565619417308481253243)
        ·
          refine ⟨422348429125962721879865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281565619417308481253243 422348429125962721879865)
          ·
            refine ⟨316761321844472041409899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422348429125962721879865 316761321844472041409899)
            ·
              refine ⟨475141982766708062114849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316761321844472041409899 475141982766708062114849)
              ·
                refine ⟨356356487075031046586137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 475141982766708062114849 356356487075031046586137)
                ·
                  refine ⟨267267365306273284939603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356356487075031046586137 267267365306273284939603)
                  ·
                    refine ⟨400901047959409927409405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 267267365306273284939603 400901047959409927409405)
                    ·
                      refine ⟨150337892984778722778527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 400901047959409927409405 150337892984778722778527)
                      ·
                        rfl

theorem cell23_292782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_292782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292782 prefixEnd_292782 := by exact prefixLift 292782
  have htrace : WordTrace (prefixWord ++ tailWord_292782) baseStart_292782 baseEnd_292782 := by
    simpa [prefixWord, tailWord_292782, baseEnd_292782] using wordTrace_append hprefix tailTrace_292782
  have hstable : (prefixWord ++ tailWord_292782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292782).length < 2 ^ (prefixWord ++ tailWord_292782).sum := by decide
  have hdescent : baseEnd_292782 < baseStart_292782 := by decide
  rcases family_descends (prefixWord ++ tailWord_292782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292800 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 7]
def baseStart_292800 : Nat := 118140960795 + 292800 * 2 ^ 59
def prefixEnd_292800 : Nat := 4983230072969 + 3 ^ 40 * 292800 * 2
def baseEnd_292800 : Nat := 150347135636559652353443

theorem tailTrace_292800 : CollatzResearch.WordTrace tailWord_292800 prefixEnd_292800 150347135636559652353443 := by
  unfold tailWord_292800
  simp only [CollatzResearch.WordTrace]
  refine ⟨5339646669621540551953927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7119528892828720735938569 5339646669621540551953927)
  ·
    refine ⟨8009470004432310827930891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5339646669621540551953927 8009470004432310827930891)
    ·
      refine ⟨12014205006648466241896337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8009470004432310827930891 12014205006648466241896337)
      ·
        refine ⟨9010653754986349681422253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12014205006648466241896337 9010653754986349681422253)
        ·
          refine ⟨3378995158119881130533345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9010653754986349681422253 3378995158119881130533345)
          ·
            refine ⟨2534246368589910847900009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3378995158119881130533345 2534246368589910847900009)
            ·
              refine ⟨1900684776442433135925007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2534246368589910847900009 1900684776442433135925007)
              ·
                refine ⟨2851027164663649703887511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1900684776442433135925007 2851027164663649703887511)
                ·
                  refine ⟨4276540746995474555831267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2851027164663649703887511 4276540746995474555831267)
                  ·
                    refine ⟨6414811120493211833746901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4276540746995474555831267 6414811120493211833746901)
                    ·
                      refine ⟨150347135636559652353443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6414811120493211833746901 150347135636559652353443)
                      ·
                        rfl

theorem cell23_292800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_292800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292800 prefixEnd_292800 := by exact prefixLift 292800
  have htrace : WordTrace (prefixWord ++ tailWord_292800) baseStart_292800 baseEnd_292800 := by
    simpa [prefixWord, tailWord_292800, baseEnd_292800] using wordTrace_append hprefix tailTrace_292800
  have hstable : (prefixWord ++ tailWord_292800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292800).length < 2 ^ (prefixWord ++ tailWord_292800).sum := by decide
  have hdescent : baseEnd_292800 < baseStart_292800 := by decide
  rcases family_descends (prefixWord ++ tailWord_292800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292880 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 2, 9]
def baseStart_292880 : Nat := 118140960795 + 292880 * 2 ^ 59
def prefixEnd_292880 : Nat := 4983230072969 + 3 ^ 40 * 292880 * 2
def baseEnd_292880 : Nat := 50129404696306446451025

theorem tailTrace_292880 : CollatzResearch.WordTrace tailWord_292880 prefixEnd_292880 50129404696306446451025 := by
  unfold tailWord_292880
  simp only [CollatzResearch.WordTrace]
  refine ⟨5341105589476627383410047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7121474119302169844546729 5341105589476627383410047)
  ·
    refine ⟨8011658384214941075115071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5341105589476627383410047 8011658384214941075115071)
    ·
      refine ⟨12017487576322411612672607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8011658384214941075115071 12017487576322411612672607)
      ·
        refine ⟨18026231364483617419008911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12017487576322411612672607 18026231364483617419008911)
        ·
          refine ⟨27039347046725426128513367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18026231364483617419008911 27039347046725426128513367)
          ·
            refine ⟨40559020570088139192770051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27039347046725426128513367 40559020570088139192770051)
            ·
              refine ⟨60838530855132208789155077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40559020570088139192770051 60838530855132208789155077)
              ·
                refine ⟨11407224535337289147966577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60838530855132208789155077 11407224535337289147966577)
                ·
                  refine ⟨8555418401502966860974933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11407224535337289147966577 8555418401502966860974933)
                  ·
                    refine ⟨50129404696306446451025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 8555418401502966860974933 50129404696306446451025)
                    ·
                      rfl

theorem cell23_292880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 9].length) (baseStart_292880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292880 prefixEnd_292880 := by exact prefixLift 292880
  have htrace : WordTrace (prefixWord ++ tailWord_292880) baseStart_292880 baseEnd_292880 := by
    simpa [prefixWord, tailWord_292880, baseEnd_292880] using wordTrace_append hprefix tailTrace_292880
  have hstable : (prefixWord ++ tailWord_292880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292880).length < 2 ^ (prefixWord ++ tailWord_292880).sum := by decide
  have hdescent : baseEnd_292880 < baseStart_292880 := by decide
  rcases family_descends (prefixWord ++ tailWord_292880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292927 : List Nat := [1, 1, 2, 2, 3, 1, 3, 3, 1, 6]
def baseStart_292927 : Nat := 118140960795 + 292927 * 2 ^ 59
def prefixEnd_292927 : Nat := 4983230072969 + 3 ^ 40 * 292927 * 2
def baseEnd_292927 : Nat := 50137449226560218488453

theorem tailTrace_292927 : CollatzResearch.WordTrace tailWord_292927 prefixEnd_292927 50137449226560218488453 := by
  unfold tailWord_292927
  simp only [CollatzResearch.WordTrace]
  refine ⟨10683925409782981793781035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7122616939855321195854023 10683925409782981793781035)
  ·
    refine ⟨16025888114674472690671553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10683925409782981793781035 16025888114674472690671553)
    ·
      refine ⟨12019416086005854518003665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16025888114674472690671553 12019416086005854518003665)
      ·
        refine ⟨9014562064504390888502749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12019416086005854518003665 9014562064504390888502749)
        ·
          refine ⟨3380460774189146583188531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9014562064504390888502749 3380460774189146583188531)
          ·
            refine ⟨5070691161283719874782797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3380460774189146583188531 5070691161283719874782797)
            ·
              refine ⟨1901509185481394953043549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5070691161283719874782797 1901509185481394953043549)
              ·
                refine ⟨713065944555523107391331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1901509185481394953043549 713065944555523107391331)
                ·
                  refine ⟨1069598916833284661086997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 713065944555523107391331 1069598916833284661086997)
                  ·
                    refine ⟨50137449226560218488453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1069598916833284661086997 50137449226560218488453)
                    ·
                      rfl

theorem cell23_292927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 6].length) (baseStart_292927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292927 prefixEnd_292927 := by exact prefixLift 292927
  have htrace : WordTrace (prefixWord ++ tailWord_292927) baseStart_292927 baseEnd_292927 := by
    simpa [prefixWord, tailWord_292927, baseEnd_292927] using wordTrace_append hprefix tailTrace_292927
  have hstable : (prefixWord ++ tailWord_292927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292927).length < 2 ^ (prefixWord ++ tailWord_292927).sum := by decide
  have hdescent : baseEnd_292927 < baseStart_292927 := by decide
  rcases family_descends (prefixWord ++ tailWord_292927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292951 : List Nat := [1, 1, 3, 2, 2, 1, 6, 1, 1, 1, 4]
def baseStart_292951 : Nat := 118140960795 + 292951 * 2 ^ 59
def prefixEnd_292951 : Nat := 4983230072969 + 3 ^ 40 * 292951 * 2
def baseEnd_292951 : Nat := 150424671215388561565249

theorem tailTrace_292951 : CollatzResearch.WordTrace tailWord_292951 prefixEnd_292951 150424671215388561565249 := by
  unfold tailWord_292951
  simp only [CollatzResearch.WordTrace]
  refine ⟨10684800761696033892654707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7123200507797355928436471 10684800761696033892654707)
  ·
    refine ⟨16027201142544050838982061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10684800761696033892654707 16027201142544050838982061)
    ·
      refine ⟨6010200428454019064618273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16027201142544050838982061 6010200428454019064618273)
      ·
        refine ⟨4507650321340514298463705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6010200428454019064618273 4507650321340514298463705)
        ·
          refine ⟨3380737741005385723847779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4507650321340514298463705 3380737741005385723847779)
          ·
            refine ⟨5071106611508078585771669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3380737741005385723847779 5071106611508078585771669)
            ·
              refine ⟨237708122414441183708047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5071106611508078585771669 237708122414441183708047)
              ·
                refine ⟨356562183621661775562071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237708122414441183708047 356562183621661775562071)
                ·
                  refine ⟨534843275432492663343107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356562183621661775562071 534843275432492663343107)
                  ·
                    refine ⟨802264913148738995014661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 534843275432492663343107 802264913148738995014661)
                    ·
                      refine ⟨150424671215388561565249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 802264913148738995014661 150424671215388561565249)
                      ·
                        rfl

theorem cell23_292951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_292951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292951 prefixEnd_292951 := by exact prefixLift 292951
  have htrace : WordTrace (prefixWord ++ tailWord_292951) baseStart_292951 baseEnd_292951 := by
    simpa [prefixWord, tailWord_292951, baseEnd_292951] using wordTrace_append hprefix tailTrace_292951
  have hstable : (prefixWord ++ tailWord_292951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292951).length < 2 ^ (prefixWord ++ tailWord_292951).sum := by decide
  have hdescent : baseEnd_292951 < baseStart_292951 := by decide
  rcases family_descends (prefixWord ++ tailWord_292951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292978 : List Nat := [3, 2, 1, 2, 2, 3, 3, 1, 2, 4]
def baseStart_292978 : Nat := 118140960795 + 292978 * 2 ^ 59
def prefixEnd_292978 : Nat := 4983230072969 + 3 ^ 40 * 292978 * 2
def baseEnd_292978 : Nat := 50146178397686651975875

theorem tailTrace_292978 : CollatzResearch.WordTrace tailWord_292978 prefixEnd_292978 50146178397686651975875 := by
  unfold tailWord_292978
  simp only [CollatzResearch.WordTrace]
  refine ⟨2671446383149554375971897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7123857021732145002591725 2671446383149554375971897)
  ·
    refine ⟨2003584787362165781978923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2671446383149554375971897 2003584787362165781978923)
    ·
      refine ⟨3005377181043248672968385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2003584787362165781978923 3005377181043248672968385)
      ·
        refine ⟨2254032885782436504726289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3005377181043248672968385 2254032885782436504726289)
        ·
          refine ⟨1690524664336827378544717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2254032885782436504726289 1690524664336827378544717)
          ·
            refine ⟨633946749126310266954269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1690524664336827378544717 633946749126310266954269)
            ·
              refine ⟨237730030922366350107851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 633946749126310266954269 237730030922366350107851)
              ·
                refine ⟨356595046383549525161777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237730030922366350107851 356595046383549525161777)
                ·
                  refine ⟨267446284787662143871333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356595046383549525161777 267446284787662143871333)
                  ·
                    refine ⟨50146178397686651975875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 267446284787662143871333 50146178397686651975875)
                    ·
                      rfl

theorem cell23_292978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_292978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_292978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_292978 prefixEnd_292978 := by exact prefixLift 292978
  have htrace : WordTrace (prefixWord ++ tailWord_292978) baseStart_292978 baseEnd_292978 := by
    simpa [prefixWord, tailWord_292978, baseEnd_292978] using wordTrace_append hprefix tailTrace_292978
  have hstable : (prefixWord ++ tailWord_292978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292978).length < 2 ^ (prefixWord ++ tailWord_292978).sum := by decide
  have hdescent : baseEnd_292978 < baseStart_292978 := by decide
  rcases family_descends (prefixWord ++ tailWord_292978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293002 : List Nat := [3, 1, 2, 3, 1, 4, 1, 3, 1, 2, 2]
def baseStart_293002 : Nat := 118140960795 + 293002 * 2 ^ 59
def prefixEnd_293002 : Nat := 4983230072969 + 3 ^ 40 * 293002 * 2
def baseEnd_293002 : Nat := 150450858728767862027515

theorem tailTrace_293002 : CollatzResearch.WordTrace tailWord_293002 prefixEnd_293002 150450858728767862027515 := by
  unfold tailWord_293002
  simp only [CollatzResearch.WordTrace]
  refine ⟨2671665221127817400690315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7124440589674179735174173 2671665221127817400690315)
  ·
    refine ⟨4007497831691726101035473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2671665221127817400690315 4007497831691726101035473)
    ·
      refine ⟨3005623373768794575776605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4007497831691726101035473 3005623373768794575776605)
      ·
        refine ⟨1127108765163297965916227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3005623373768794575776605 1127108765163297965916227)
        ·
          refine ⟨1690663147744946948874341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127108765163297965916227 1690663147744946948874341)
          ·
            refine ⟨316999340202177552913939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1690663147744946948874341 316999340202177552913939)
            ·
              refine ⟨475499010303266329370909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316999340202177552913939 475499010303266329370909)
              ·
                refine ⟨178312128863724873514091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 475499010303266329370909 178312128863724873514091)
                ·
                  refine ⟨267468193295587310271137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178312128863724873514091 267468193295587310271137)
                  ·
                    refine ⟨200601144971690482703353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 267468193295587310271137 200601144971690482703353)
                    ·
                      refine ⟨150450858728767862027515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 200601144971690482703353 150450858728767862027515)
                      ·
                        rfl

theorem cell23_293002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_293002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293002 prefixEnd_293002 := by exact prefixLift 293002
  have htrace : WordTrace (prefixWord ++ tailWord_293002) baseStart_293002 baseEnd_293002 := by
    simpa [prefixWord, tailWord_293002, baseEnd_293002] using wordTrace_append hprefix tailTrace_293002
  have hstable : (prefixWord ++ tailWord_293002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293002).length < 2 ^ (prefixWord ++ tailWord_293002).sum := by decide
  have hdescent : baseEnd_293002 < baseStart_293002 := by decide
  rcases family_descends (prefixWord ++ tailWord_293002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293017 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 4, 6]
def baseStart_293017 : Nat := 118140960795 + 293017 * 2 ^ 59
def prefixEnd_293017 : Nat := 4983230072969 + 3 ^ 40 * 293017 * 2
def baseEnd_293017 : Nat := 50152853646195101113315

theorem tailTrace_293017 : CollatzResearch.WordTrace tailWord_293017 prefixEnd_293017 50152853646195101113315 := by
  unfold tailWord_293017
  simp only [CollatzResearch.WordTrace]
  refine ⟨10687207979456927164557305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7124805319637951443038203 10687207979456927164557305)
  ·
    refine ⟨8015405984592695373417979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10687207979456927164557305 8015405984592695373417979)
    ·
      refine ⟨12023108976889043060126969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8015405984592695373417979 12023108976889043060126969)
      ·
        refine ⟨9017331732666782295095227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12023108976889043060126969 9017331732666782295095227)
        ·
          refine ⟨13525997599000173442642841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9017331732666782295095227 13525997599000173442642841)
          ·
            refine ⟨10144498199250130081982131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13525997599000173442642841 10144498199250130081982131)
            ·
              refine ⟨15216747298875195122973197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10144498199250130081982131 15216747298875195122973197)
              ·
                refine ⟨5706280237078198171114949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15216747298875195122973197 5706280237078198171114949)
                ·
                  refine ⟨1069927544452162157084053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5706280237078198171114949 1069927544452162157084053)
                  ·
                    refine ⟨50152853646195101113315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1069927544452162157084053 50152853646195101113315)
                    ·
                      rfl

theorem cell23_293017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 6].length) (baseStart_293017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293017 prefixEnd_293017 := by exact prefixLift 293017
  have htrace : WordTrace (prefixWord ++ tailWord_293017) baseStart_293017 baseEnd_293017 := by
    simpa [prefixWord, tailWord_293017, baseEnd_293017] using wordTrace_append hprefix tailTrace_293017
  have hstable : (prefixWord ++ tailWord_293017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293017).length < 2 ^ (prefixWord ++ tailWord_293017).sum := by decide
  have hdescent : baseEnd_293017 < baseStart_293017 := by decide
  rcases family_descends (prefixWord ++ tailWord_293017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293045 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 3, 3, 2]
def baseStart_293045 : Nat := 118140960795 + 293045 * 2 ^ 59
def prefixEnd_293045 : Nat := 4983230072969 + 3 ^ 40 * 293045 * 2
def baseEnd_293045 : Nat := 150472938396911193789817

theorem tailTrace_293045 : CollatzResearch.WordTrace tailWord_293045 prefixEnd_293045 150472938396911193789817 := by
  unfold tailWord_293045
  simp only [CollatzResearch.WordTrace]
  refine ⟨10688229223355487946576589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7125486148903658631051059 10688229223355487946576589)
  ·
    refine ⟨4008085958758307979966221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10688229223355487946576589 4008085958758307979966221)
    ·
      refine ⟨1503032234534365492487333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4008085958758307979966221 1503032234534365492487333)
      ·
        refine ⟨281818543975193529841375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1503032234534365492487333 281818543975193529841375)
        ·
          refine ⟨422727815962790294762063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281818543975193529841375 422727815962790294762063)
          ·
            refine ⟨634091723944185442143095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422727815962790294762063 634091723944185442143095)
            ·
              refine ⟨951137585916278163214643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634091723944185442143095 951137585916278163214643)
              ·
                refine ⟨1426706378874417244821965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951137585916278163214643 1426706378874417244821965)
                ·
                  refine ⟨535014892077906466808237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1426706378874417244821965 535014892077906466808237)
                  ·
                    refine ⟨200630584529214925053089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 535014892077906466808237 200630584529214925053089)
                    ·
                      refine ⟨150472938396911193789817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 200630584529214925053089 150472938396911193789817)
                      ·
                        rfl

theorem cell23_293045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_293045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293045 prefixEnd_293045 := by exact prefixLift 293045
  have htrace : WordTrace (prefixWord ++ tailWord_293045) baseStart_293045 baseEnd_293045 := by
    simpa [prefixWord, tailWord_293045, baseEnd_293045] using wordTrace_append hprefix tailTrace_293045
  have hstable : (prefixWord ++ tailWord_293045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293045).length < 2 ^ (prefixWord ++ tailWord_293045).sum := by decide
  have hdescent : baseEnd_293045 < baseStart_293045 := by decide
  rcases family_descends (prefixWord ++ tailWord_293045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293078 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_293078 : Nat := 118140960795 + 293078 * 2 ^ 59
def prefixEnd_293078 : Nat := 4983230072969 + 3 ^ 40 * 293078 * 2
def baseEnd_293078 : Nat := 150489883258509564677165

theorem tailTrace_293078 : CollatzResearch.WordTrace tailWord_293078 prefixEnd_293078 150489883258509564677165 := by
  unfold tailWord_293078
  simp only [CollatzResearch.WordTrace]
  refine ⟨668089552014745911407993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7126288554823956388351925 668089552014745911407993)
  ·
    refine ⟨501067164011059433555995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 668089552014745911407993 501067164011059433555995)
    ·
      refine ⟨751600746016589150333993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 501067164011059433555995 751600746016589150333993)
      ·
        refine ⟨563700559512441862750495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 751600746016589150333993 563700559512441862750495)
        ·
          refine ⟨845550839268662794125743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563700559512441862750495 845550839268662794125743)
          ·
            refine ⟨1268326258902994191188615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845550839268662794125743 1268326258902994191188615)
            ·
              refine ⟨1902489388354491286782923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1268326258902994191188615 1902489388354491286782923)
              ·
                refine ⟨2853734082531736930174385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1902489388354491286782923 2853734082531736930174385)
                ·
                  refine ⟨2140300561898802697630789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2853734082531736930174385 2140300561898802697630789)
                  ·
                    refine ⟨401306355356025505805773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2140300561898802697630789 401306355356025505805773)
                    ·
                      refine ⟨150489883258509564677165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 401306355356025505805773 150489883258509564677165)
                      ·
                        rfl

theorem cell23_293078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_293078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293078 prefixEnd_293078 := by exact prefixLift 293078
  have htrace : WordTrace (prefixWord ++ tailWord_293078) baseStart_293078 baseEnd_293078 := by
    simpa [prefixWord, tailWord_293078, baseEnd_293078] using wordTrace_append hprefix tailTrace_293078
  have hstable : (prefixWord ++ tailWord_293078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293078).length < 2 ^ (prefixWord ++ tailWord_293078).sum := by decide
  have hdescent : baseEnd_293078 < baseStart_293078 := by decide
  rcases family_descends (prefixWord ++ tailWord_293078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293131 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 4, 4, 2]
def baseStart_293131 : Nat := 118140960795 + 293131 * 2 ^ 59
def prefixEnd_293131 : Nat := 4983230072969 + 3 ^ 40 * 293131 * 2
def baseEnd_293131 : Nat := 150517097733197857314421

theorem tailTrace_293131 : CollatzResearch.WordTrace tailWord_293131 prefixEnd_293131 150517097733197857314421 := by
  unfold tailWord_293131
  simp only [CollatzResearch.WordTrace]
  refine ⟨10691365901043924634207247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7127577267362616422804831 10691365901043924634207247)
  ·
    refine ⟨16037048851565886951310871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10691365901043924634207247 16037048851565886951310871)
    ·
      refine ⟨24055573277348830426966307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16037048851565886951310871 24055573277348830426966307)
      ·
        refine ⟨36083359916023245640449461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24055573277348830426966307 36083359916023245640449461)
        ·
          refine ⟨3382814992127179278792137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36083359916023245640449461 3382814992127179278792137)
          ·
            refine ⟨2537111244095384459094103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3382814992127179278792137 2537111244095384459094103)
            ·
              refine ⟨3805666866143076688641155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2537111244095384459094103 3805666866143076688641155)
              ·
                refine ⟨5708500299214615032961733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3805666866143076688641155 5708500299214615032961733)
                ·
                  refine ⟨1070343806102740318680325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5708500299214615032961733 1070343806102740318680325)
                  ·
                    refine ⟨200689463644263809752561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1070343806102740318680325 200689463644263809752561)
                    ·
                      refine ⟨150517097733197857314421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 200689463644263809752561 150517097733197857314421)
                      ·
                        rfl

theorem cell23_293131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 4, 2].length) (baseStart_293131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293131 prefixEnd_293131 := by exact prefixLift 293131
  have htrace : WordTrace (prefixWord ++ tailWord_293131) baseStart_293131 baseEnd_293131 := by
    simpa [prefixWord, tailWord_293131, baseEnd_293131] using wordTrace_append hprefix tailTrace_293131
  have hstable : (prefixWord ++ tailWord_293131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293131).length < 2 ^ (prefixWord ++ tailWord_293131).sum := by decide
  have hdescent : baseEnd_293131 < baseStart_293131 := by decide
  rcases family_descends (prefixWord ++ tailWord_293131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293141 : List Nat := [1, 3, 2, 1, 2, 1, 3, 3, 3, 4]
def baseStart_293141 : Nat := 118140960795 + 293141 * 2 ^ 59
def prefixEnd_293141 : Nat := 4983230072969 + 3 ^ 40 * 293141 * 2
def baseEnd_293141 : Nat := 50174077513247606063125

theorem tailTrace_293141 : CollatzResearch.WordTrace tailWord_293141 prefixEnd_293141 50174077513247606063125 := by
  unfold tailWord_293141
  simp only [CollatzResearch.WordTrace]
  refine ⟨10691730631007696342071277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7127820420671797561380851 10691730631007696342071277)
  ·
    refine ⟨4009398986627886128276729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10691730631007696342071277 4009398986627886128276729)
    ·
      refine ⟨3007049239970914596207547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4009398986627886128276729 3007049239970914596207547)
      ·
        refine ⟨4510573859956371894311321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3007049239970914596207547 4510573859956371894311321)
        ·
          refine ⟨3382930394967278920733491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4510573859956371894311321 3382930394967278920733491)
          ·
            refine ⟨5074395592450918381100237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3382930394967278920733491 5074395592450918381100237)
            ·
              refine ⟨1902898347169094392912589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5074395592450918381100237 1902898347169094392912589)
              ·
                refine ⟨713586880188410397342221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1902898347169094392912589 713586880188410397342221)
                ·
                  refine ⟨267595080070653899003333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713586880188410397342221 267595080070653899003333)
                  ·
                    refine ⟨50174077513247606063125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 267595080070653899003333 50174077513247606063125)
                    ·
                      rfl

theorem cell23_293141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_293141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293141 prefixEnd_293141 := by exact prefixLift 293141
  have htrace : WordTrace (prefixWord ++ tailWord_293141) baseStart_293141 baseEnd_293141 := by
    simpa [prefixWord, tailWord_293141, baseEnd_293141] using wordTrace_append hprefix tailTrace_293141
  have hstable : (prefixWord ++ tailWord_293141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293141).length < 2 ^ (prefixWord ++ tailWord_293141).sum := by decide
  have hdescent : baseEnd_293141 < baseStart_293141 := by decide
  rcases family_descends (prefixWord ++ tailWord_293141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293144 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 2, 1, 6]
def baseStart_293144 : Nat := 118140960795 + 293144 * 2 ^ 59
def prefixEnd_293144 : Nat := 4983230072969 + 3 ^ 40 * 293144 * 2
def baseEnd_293144 : Nat := 150523772981706306451861

theorem tailTrace_293144 : CollatzResearch.WordTrace tailWord_293144 prefixEnd_293144 150523772981706306451861 := by
  unfold tailWord_293144
  simp only [CollatzResearch.WordTrace]
  refine ⟨5345920024998413927215243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7127893366664551902953657 5345920024998413927215243)
  ·
    refine ⟨8018880037497620890822865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5345920024998413927215243 8018880037497620890822865)
    ·
      refine ⟨6014160028123215668117149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8018880037497620890822865 6014160028123215668117149)
      ·
        refine ⟨2255310010546205875543931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6014160028123215668117149 2255310010546205875543931)
        ·
          refine ⟨3382965015819308813315897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2255310010546205875543931 3382965015819308813315897)
          ·
            refine ⟨2537223761864481609986923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3382965015819308813315897 2537223761864481609986923)
            ·
              refine ⟨3805835642796722414980385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2537223761864481609986923 3805835642796722414980385)
              ·
                refine ⟨2854376732097541811235289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3805835642796722414980385 2854376732097541811235289)
                ·
                  refine ⟨2140782549073156358426467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2854376732097541811235289 2140782549073156358426467)
                  ·
                    refine ⟨3211173823609734537639701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2140782549073156358426467 3211173823609734537639701)
                    ·
                      refine ⟨150523772981706306451861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3211173823609734537639701 150523772981706306451861)
                      ·
                        rfl

theorem cell23_293144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_293144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293144 prefixEnd_293144 := by exact prefixLift 293144
  have htrace : WordTrace (prefixWord ++ tailWord_293144) baseStart_293144 baseEnd_293144 := by
    simpa [prefixWord, tailWord_293144, baseEnd_293144] using wordTrace_append hprefix tailTrace_293144
  have hstable : (prefixWord ++ tailWord_293144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293144).length < 2 ^ (prefixWord ++ tailWord_293144).sum := by decide
  have hdescent : baseEnd_293144 < baseStart_293144 := by decide
  rcases family_descends (prefixWord ++ tailWord_293144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293151 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 3]
def baseStart_293151 : Nat := 118140960795 + 293151 * 2 ^ 59
def prefixEnd_293151 : Nat := 4983230072969 + 3 ^ 40 * 293151 * 2
def baseEnd_293151 : Nat := 150527367346287779064329

theorem tailTrace_293151 : CollatzResearch.WordTrace tailWord_293151 prefixEnd_293151 150527367346287779064329 := by
  unfold tailWord_293151
  simp only [CollatzResearch.WordTrace]
  refine ⟨10692095360971468049935307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7128063573980978699956871 10692095360971468049935307)
  ·
    refine ⟨16038143041457202074902961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10692095360971468049935307 16038143041457202074902961)
    ·
      refine ⟨12028607281092901556177221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16038143041457202074902961 12028607281092901556177221)
      ·
        refine ⟨2255363865204919041783229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12028607281092901556177221 2255363865204919041783229)
        ·
          refine ⟨845761449451844640668711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2255363865204919041783229 845761449451844640668711)
          ·
            refine ⟨1268642174177766961003067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845761449451844640668711 1268642174177766961003067)
            ·
              refine ⟨1902963261266650441504601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1268642174177766961003067 1902963261266650441504601)
              ·
                refine ⟨1427222445949987831128451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1902963261266650441504601 1427222445949987831128451)
                ·
                  refine ⟨2140833668924981746692677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427222445949987831128451 2140833668924981746692677)
                  ·
                    refine ⟨401406312923434077504877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2140833668924981746692677 401406312923434077504877)
                    ·
                      refine ⟨150527367346287779064329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 401406312923434077504877 150527367346287779064329)
                      ·
                        rfl

theorem cell23_293151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_293151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293151 prefixEnd_293151 := by exact prefixLift 293151
  have htrace : WordTrace (prefixWord ++ tailWord_293151) baseStart_293151 baseEnd_293151 := by
    simpa [prefixWord, tailWord_293151, baseEnd_293151] using wordTrace_append hprefix tailTrace_293151
  have hstable : (prefixWord ++ tailWord_293151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293151).length < 2 ^ (prefixWord ++ tailWord_293151).sum := by decide
  have hdescent : baseEnd_293151 < baseStart_293151 := by decide
  rcases family_descends (prefixWord ++ tailWord_293151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293185 : List Nat := [1, 2, 5, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_293185 : Nat := 118140960795 + 293185 * 2 ^ 59
def prefixEnd_293185 : Nat := 4983230072969 + 3 ^ 40 * 293185 * 2
def baseEnd_293185 : Nat := 150544825688540646039173

theorem tailTrace_293185 : CollatzResearch.WordTrace tailWord_293185 prefixEnd_293185 150544825688540646039173 := by
  unfold tailWord_293185
  simp only [CollatzResearch.WordTrace]
  refine ⟨10693335442848291856673009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7128890295232194571115339 10693335442848291856673009)
  ·
    refine ⟨8020001582136218892504757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10693335442848291856673009 8020001582136218892504757)
    ·
      refine ⟨751875148325270521172321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8020001582136218892504757 751875148325270521172321)
      ·
        refine ⟨563906361243952890879241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 751875148325270521172321 563906361243952890879241)
        ·
          refine ⟨422929770932964668159431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 563906361243952890879241 422929770932964668159431)
          ·
            refine ⟨634394656399447002239147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422929770932964668159431 634394656399447002239147)
            ·
              refine ⟨951591984599170503358721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634394656399447002239147 951591984599170503358721)
              ·
                refine ⟨713693988449377877519041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 951591984599170503358721 713693988449377877519041)
                ·
                  refine ⟨535270491337033408139281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 713693988449377877519041 535270491337033408139281)
                  ·
                    refine ⟨401452868502775056104461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 535270491337033408139281 401452868502775056104461)
                    ·
                      refine ⟨150544825688540646039173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 401452868502775056104461 150544825688540646039173)
                      ·
                        rfl

theorem cell23_293185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_293185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293185 prefixEnd_293185 := by exact prefixLift 293185
  have htrace : WordTrace (prefixWord ++ tailWord_293185) baseStart_293185 baseEnd_293185 := by
    simpa [prefixWord, tailWord_293185, baseEnd_293185] using wordTrace_append hprefix tailTrace_293185
  have hstable : (prefixWord ++ tailWord_293185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293185).length < 2 ^ (prefixWord ++ tailWord_293185).sum := by decide
  have hdescent : baseEnd_293185 < baseStart_293185 := by decide
  rcases family_descends (prefixWord ++ tailWord_293185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293194 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_293194 : Nat := 118140960795 + 293194 * 2 ^ 59
def prefixEnd_293194 : Nat := 4983230072969 + 3 ^ 40 * 293194 * 2
def baseEnd_293194 : Nat := 150549447014431110826631

theorem tailTrace_293194 : CollatzResearch.WordTrace tailWord_293194 prefixEnd_293194 150549447014431110826631 := by
  unfold tailWord_293194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2673415924953921598437659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7129109133210457595833757 2673415924953921598437659)
  ·
    refine ⟨4010123887430882397656489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2673415924953921598437659 4010123887430882397656489)
    ·
      refine ⟨3007592915573161798242367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4010123887430882397656489 3007592915573161798242367)
      ·
        refine ⟨4511389373359742697363551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3007592915573161798242367 4511389373359742697363551)
        ·
          refine ⟨6767084060039614046045327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4511389373359742697363551 6767084060039614046045327)
          ·
            refine ⟨10150626090059421069067991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6767084060039614046045327 10150626090059421069067991)
            ·
              refine ⟨15225939135089131603601987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10150626090059421069067991 15225939135089131603601987)
              ·
                refine ⟨22838908702633697405402981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15225939135089131603601987 22838908702633697405402981)
                ·
                  refine ⟨4282295381743818263513059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22838908702633697405402981 4282295381743818263513059)
                  ·
                    refine ⟨6423443072615727395269589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4282295381743818263513059 6423443072615727395269589)
                    ·
                      refine ⟨150549447014431110826631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6423443072615727395269589 150549447014431110826631)
                      ·
                        rfl

theorem cell23_293194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_293194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293194 prefixEnd_293194 := by exact prefixLift 293194
  have htrace : WordTrace (prefixWord ++ tailWord_293194) baseStart_293194 baseEnd_293194 := by
    simpa [prefixWord, tailWord_293194, baseEnd_293194] using wordTrace_append hprefix tailTrace_293194
  have hstable : (prefixWord ++ tailWord_293194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293194).length < 2 ^ (prefixWord ++ tailWord_293194).sum := by decide
  have hdescent : baseEnd_293194 < baseStart_293194 := by decide
  rcases family_descends (prefixWord ++ tailWord_293194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293198 : List Nat := [4, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3]
def baseStart_293198 : Nat := 118140960795 + 293198 * 2 ^ 59
def prefixEnd_293198 : Nat := 4983230072969 + 3 ^ 40 * 293198 * 2
def baseEnd_293198 : Nat := 150551500937049095176613

theorem tailTrace_293198 : CollatzResearch.WordTrace tailWord_293198 prefixEnd_293198 150551500937049095176613 := by
  unfold tailWord_293198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1336726198975149384612031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7129206394534130051264165 1336726198975149384612031)
  ·
    refine ⟨2005089298462724076918047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1336726198975149384612031 2005089298462724076918047)
    ·
      refine ⟨3007633947694086115377071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2005089298462724076918047 3007633947694086115377071)
      ·
        refine ⟨4511450921541129173065607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3007633947694086115377071 4511450921541129173065607)
        ·
          refine ⟨6767176382311693759598411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4511450921541129173065607 6767176382311693759598411)
          ·
            refine ⟨10150764573467540639397617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6767176382311693759598411 10150764573467540639397617)
            ·
              refine ⟨7613073430100655479548213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10150764573467540639397617 7613073430100655479548213)
              ·
                refine ⟨713725634071936451207645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7613073430100655479548213 713725634071936451207645)
                ·
                  refine ⟨267647112776976169202867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713725634071936451207645 267647112776976169202867)
                  ·
                    refine ⟨401470669165464253804301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 267647112776976169202867 401470669165464253804301)
                    ·
                      refine ⟨150551500937049095176613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 401470669165464253804301 150551500937049095176613)
                      ·
                        rfl

theorem cell23_293198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_293198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293198 prefixEnd_293198 := by exact prefixLift 293198
  have htrace : WordTrace (prefixWord ++ tailWord_293198) baseStart_293198 baseEnd_293198 := by
    simpa [prefixWord, tailWord_293198, baseEnd_293198] using wordTrace_append hprefix tailTrace_293198
  have hstable : (prefixWord ++ tailWord_293198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293198).length < 2 ^ (prefixWord ++ tailWord_293198).sum := by decide
  have hdescent : baseEnd_293198 < baseStart_293198 := by decide
  rcases family_descends (prefixWord ++ tailWord_293198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293205 : List Nat := [1, 3, 2, 2, 4, 2, 2, 1, 6]
def baseStart_293205 : Nat := 118140960795 + 293205 * 2 ^ 59
def prefixEnd_293205 : Nat := 4983230072969 + 3 ^ 40 * 293205 * 2
def baseEnd_293205 : Nat := 16728343922403396421009

theorem tailTrace_293205 : CollatzResearch.WordTrace tailWord_293205 prefixEnd_293205 16728343922403396421009 := by
  unfold tailWord_293205
  simp only [CollatzResearch.WordTrace]
  refine ⟨10694064902775835272401069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7129376601850556848267379 10694064902775835272401069)
  ·
    refine ⟨4010274338540938227150401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10694064902775835272401069 4010274338540938227150401)
    ·
      refine ⟨3007705753905703670362801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4010274338540938227150401 3007705753905703670362801)
      ·
        refine ⟨2255779315429277752772101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3007705753905703670362801 2255779315429277752772101)
        ·
          refine ⟨422958621642989578644769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2255779315429277752772101 422958621642989578644769)
          ·
            refine ⟨317218966232242183983577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422958621642989578644769 317218966232242183983577)
            ·
              refine ⟨237914224674181637987683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317218966232242183983577 237914224674181637987683)
              ·
                refine ⟨356871337011272456981525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237914224674181637987683 356871337011272456981525)
                ·
                  refine ⟨16728343922403396421009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 356871337011272456981525 16728343922403396421009)
                  ·
                    rfl

theorem cell23_293205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 6].length) (baseStart_293205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293205 prefixEnd_293205 := by exact prefixLift 293205
  have htrace : WordTrace (prefixWord ++ tailWord_293205) baseStart_293205 baseEnd_293205 := by
    simpa [prefixWord, tailWord_293205, baseEnd_293205] using wordTrace_append hprefix tailTrace_293205
  have hstable : (prefixWord ++ tailWord_293205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293205).length < 2 ^ (prefixWord ++ tailWord_293205).sum := by decide
  have hdescent : baseEnd_293205 < baseStart_293205 := by decide
  rcases family_descends (prefixWord ++ tailWord_293205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293218 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_293218 : Nat := 118140960795 + 293218 * 2 ^ 59
def prefixEnd_293218 : Nat := 4983230072969 + 3 ^ 40 * 293218 * 2
def baseEnd_293218 : Nat := 50187256850046338975507

theorem tailTrace_293218 : CollatzResearch.WordTrace tailWord_293218 prefixEnd_293218 50187256850046338975507 := by
  unfold tailWord_293218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2673634762932184623156077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7129692701152492328416205 2673634762932184623156077)
  ·
    refine ⟨1002613036099569233683529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2673634762932184623156077 1002613036099569233683529)
    ·
      refine ⟨751959777074676925262647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1002613036099569233683529 751959777074676925262647)
      ·
        refine ⟨1127939665612015387893971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 751959777074676925262647 1127939665612015387893971)
        ·
          refine ⟨1691909498418023081840957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127939665612015387893971 1691909498418023081840957)
          ·
            refine ⟨634466061906758655690359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1691909498418023081840957 634466061906758655690359)
            ·
              refine ⟨951699092860137983535539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634466061906758655690359 951699092860137983535539)
              ·
                refine ⟨1427548639290206975303309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951699092860137983535539 1427548639290206975303309)
                ·
                  refine ⟨535330739733827615738741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1427548639290206975303309 535330739733827615738741)
                  ·
                    refine ⟨50187256850046338975507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 535330739733827615738741 50187256850046338975507)
                    ·
                      rfl

theorem cell23_293218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_293218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293218 prefixEnd_293218 := by exact prefixLift 293218
  have htrace : WordTrace (prefixWord ++ tailWord_293218) baseStart_293218 baseEnd_293218 := by
    simpa [prefixWord, tailWord_293218, baseEnd_293218] using wordTrace_append hprefix tailTrace_293218
  have hstable : (prefixWord ++ tailWord_293218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293218).length < 2 ^ (prefixWord ++ tailWord_293218).sum := by decide
  have hdescent : baseEnd_293218 < baseStart_293218 := by decide
  rcases family_descends (prefixWord ++ tailWord_293218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293231 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 4, 4]
def baseStart_293231 : Nat := 118140960795 + 293231 * 2 ^ 59
def prefixEnd_293231 : Nat := 4983230072969 + 3 ^ 40 * 293231 * 2
def baseEnd_293231 : Nat := 50189481932882488687987

theorem tailTrace_293231 : CollatzResearch.WordTrace tailWord_293231 prefixEnd_293231 50189481932882488687987 := by
  unfold tailWord_293231
  simp only [CollatzResearch.WordTrace]
  refine ⟨10695013200681641712847547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7130008800454427808565031 10695013200681641712847547)
  ·
    refine ⟨16042519801022462569271321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10695013200681641712847547 16042519801022462569271321)
    ·
      refine ⟨12031889850766846926953491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16042519801022462569271321 12031889850766846926953491)
      ·
        refine ⟨18047834776150270390430237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12031889850766846926953491 18047834776150270390430237)
        ·
          refine ⟨6767938041056351396411339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18047834776150270390430237 6767938041056351396411339)
          ·
            refine ⟨10151907061584527094617009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6767938041056351396411339 10151907061584527094617009)
            ·
              refine ⟨7613930296188395320962757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10151907061584527094617009 7613930296188395320962757)
              ·
                refine ⟨1427611930535324122680517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7613930296188395320962757 1427611930535324122680517)
                ·
                  refine ⟨267677236975373273002597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1427611930535324122680517 267677236975373273002597)
                  ·
                    refine ⟨50189481932882488687987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 267677236975373273002597 50189481932882488687987)
                    ·
                      rfl

theorem cell23_293231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 4].length) (baseStart_293231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293231 prefixEnd_293231 := by exact prefixLift 293231
  have htrace : WordTrace (prefixWord ++ tailWord_293231) baseStart_293231 baseEnd_293231 := by
    simpa [prefixWord, tailWord_293231, baseEnd_293231] using wordTrace_append hprefix tailTrace_293231
  have hstable : (prefixWord ++ tailWord_293231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293231).length < 2 ^ (prefixWord ++ tailWord_293231).sum := by decide
  have hdescent : baseEnd_293231 < baseStart_293231 := by decide
  rcases family_descends (prefixWord ++ tailWord_293231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293249 : List Nat := [1, 2, 4, 3, 1, 1, 4, 2, 1, 1, 3]
def baseStart_293249 : Nat := 118140960795 + 293249 * 2 ^ 59
def prefixEnd_293249 : Nat := 4983230072969 + 3 ^ 40 * 293249 * 2
def baseEnd_293249 : Nat := 150577688450428395638879

theorem tailTrace_293249 : CollatzResearch.WordTrace tailWord_293249 prefixEnd_293249 150577688450428395638879 := by
  unfold tailWord_293249
  simp only [CollatzResearch.WordTrace]
  refine ⟨10695669714616430787002801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7130446476410953858001867 10695669714616430787002801)
  ·
    refine ⟨8021752285962323090252101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10695669714616430787002801 8021752285962323090252101)
    ·
      refine ⟨1504078553617935579422269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8021752285962323090252101 1504078553617935579422269)
      ·
        refine ⟨564029457606725842283351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1504078553617935579422269 564029457606725842283351)
        ·
          refine ⟨846044186410088763425027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564029457606725842283351 846044186410088763425027)
          ·
            refine ⟨1269066279615133145137541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846044186410088763425027 1269066279615133145137541)
            ·
              refine ⟨237949927427837464713289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1269066279615133145137541 237949927427837464713289)
              ·
                refine ⟨178462445570878098534967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 237949927427837464713289 178462445570878098534967)
                ·
                  refine ⟨267693668356317147802451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178462445570878098534967 267693668356317147802451)
                  ·
                    refine ⟨401540502534475721703677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 267693668356317147802451 401540502534475721703677)
                    ·
                      refine ⟨150577688450428395638879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 401540502534475721703677 150577688450428395638879)
                      ·
                        rfl

theorem cell23_293249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_293249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293249 prefixEnd_293249 := by exact prefixLift 293249
  have htrace : WordTrace (prefixWord ++ tailWord_293249) baseStart_293249 baseEnd_293249 := by
    simpa [prefixWord, tailWord_293249, baseEnd_293249] using wordTrace_append hprefix tailTrace_293249
  have hstable : (prefixWord ++ tailWord_293249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293249).length < 2 ^ (prefixWord ++ tailWord_293249).sum := by decide
  have hdescent : baseEnd_293249 < baseStart_293249 := by decide
  rcases family_descends (prefixWord ++ tailWord_293249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293255 : List Nat := [1, 1, 4, 2, 2, 1, 2, 3, 3, 2, 2]
def baseStart_293255 : Nat := 118140960795 + 293255 * 2 ^ 59
def prefixEnd_293255 : Nat := 4983230072969 + 3 ^ 40 * 293255 * 2
def baseEnd_293255 : Nat := 150580769334355372163851

theorem tailTrace_293255 : CollatzResearch.WordTrace tailWord_293255 prefixEnd_293255 150580769334355372163851 := by
  unfold tailWord_293255
  simp only [CollatzResearch.WordTrace]
  refine ⟨10695888552594693811721219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7130592368396462541147479 10695888552594693811721219)
  ·
    refine ⟨16043832828892040717581829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10695888552594693811721219 16043832828892040717581829)
    ·
      refine ⟨3008218655417257634546593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16043832828892040717581829 3008218655417257634546593)
      ·
        refine ⟨2256163991562943225909945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3008218655417257634546593 2256163991562943225909945)
        ·
          refine ⟨1692122993672207419432459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2256163991562943225909945 1692122993672207419432459)
          ·
            refine ⟨2538184490508311129148689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692122993672207419432459 2538184490508311129148689)
            ·
              refine ⟨1903638367881233346861517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2538184490508311129148689 1903638367881233346861517)
              ·
                refine ⟨713864387955462505073069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1903638367881233346861517 713864387955462505073069)
                ·
                  refine ⟨267699145483298439402401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713864387955462505073069 267699145483298439402401)
                  ·
                    refine ⟨200774359112473829551801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 267699145483298439402401 200774359112473829551801)
                    ·
                      refine ⟨150580769334355372163851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 200774359112473829551801 150580769334355372163851)
                      ·
                        rfl

theorem cell23_293255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_293255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293255 prefixEnd_293255 := by exact prefixLift 293255
  have htrace : WordTrace (prefixWord ++ tailWord_293255) baseStart_293255 baseEnd_293255 := by
    simpa [prefixWord, tailWord_293255, baseEnd_293255] using wordTrace_append hprefix tailTrace_293255
  have hstable : (prefixWord ++ tailWord_293255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293255).length < 2 ^ (prefixWord ++ tailWord_293255).sum := by decide
  have hdescent : baseEnd_293255 < baseStart_293255 := by decide
  rcases family_descends (prefixWord ++ tailWord_293255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293272 : List Nat := [2, 1, 2, 5, 1, 2, 1, 2, 3, 2, 2]
def baseStart_293272 : Nat := 118140960795 + 293272 * 2 ^ 59
def prefixEnd_293272 : Nat := 4983230072969 + 3 ^ 40 * 293272 * 2
def baseEnd_293272 : Nat := 150589498505481805651273

theorem tailTrace_293272 : CollatzResearch.WordTrace tailWord_293272 prefixEnd_293272 150589498505481805651273 := by
  unfold tailWord_293272
  simp only [CollatzResearch.WordTrace]
  refine ⟨5348254296766552857545035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7131005729022070476726713 5348254296766552857545035)
  ·
    refine ⟨8022381445149829286317553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5348254296766552857545035 8022381445149829286317553)
    ·
      refine ⟨6016786083862371964738165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8022381445149829286317553 6016786083862371964738165)
      ·
        refine ⟨564073695362097371694203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6016786083862371964738165 564073695362097371694203)
        ·
          refine ⟨846110543043146057541305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564073695362097371694203 846110543043146057541305)
          ·
            refine ⟨634582907282359543155979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 846110543043146057541305 634582907282359543155979)
            ·
              refine ⟨951874360923539314733969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634582907282359543155979 951874360923539314733969)
              ·
                refine ⟨713905770692654486050477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 951874360923539314733969 713905770692654486050477)
                ·
                  refine ⟨267714664009745432268929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713905770692654486050477 267714664009745432268929)
                  ·
                    refine ⟨200785998007309074201697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 267714664009745432268929 200785998007309074201697)
                    ·
                      refine ⟨150589498505481805651273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 200785998007309074201697 150589498505481805651273)
                      ·
                        rfl

theorem cell23_293272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_293272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293272 prefixEnd_293272 := by exact prefixLift 293272
  have htrace : WordTrace (prefixWord ++ tailWord_293272) baseStart_293272 baseEnd_293272 := by
    simpa [prefixWord, tailWord_293272, baseEnd_293272] using wordTrace_append hprefix tailTrace_293272
  have hstable : (prefixWord ++ tailWord_293272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293272).length < 2 ^ (prefixWord ++ tailWord_293272).sum := by decide
  have hdescent : baseEnd_293272 < baseStart_293272 := by decide
  rcases family_descends (prefixWord ++ tailWord_293272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293305 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 4, 1, 3]
def baseStart_293305 : Nat := 118140960795 + 293305 * 2 ^ 59
def prefixEnd_293305 : Nat := 4983230072969 + 3 ^ 40 * 293305 * 2
def baseEnd_293305 : Nat := 150606443367080176538621

theorem tailTrace_293305 : CollatzResearch.WordTrace tailWord_293305 prefixEnd_293305 150606443367080176538621 := by
  unfold tailWord_293305
  simp only [CollatzResearch.WordTrace]
  refine ⟨10697712202413552351041369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7131808134942368234027579 10697712202413552351041369)
  ·
    refine ⟨8023284151810164263281027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10697712202413552351041369 8023284151810164263281027)
    ·
      refine ⟨12034926227715246394921541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8023284151810164263281027 12034926227715246394921541)
      ·
        refine ⟨2256548667696608699047789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12034926227715246394921541 2256548667696608699047789)
        ·
          refine ⟨846205750386228262142921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2256548667696608699047789 846205750386228262142921)
          ·
            refine ⟨634654312789671196607191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 846205750386228262142921 634654312789671196607191)
            ·
              refine ⟨951981469184506794910787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634654312789671196607191 951981469184506794910787)
              ·
                refine ⟨1427972203776760192366181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951981469184506794910787 1427972203776760192366181)
                ·
                  refine ⟨267744788208142536068659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1427972203776760192366181 267744788208142536068659)
                  ·
                    refine ⟨401617182312213804102989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 267744788208142536068659 401617182312213804102989)
                    ·
                      refine ⟨150606443367080176538621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 401617182312213804102989 150606443367080176538621)
                      ·
                        rfl

theorem cell23_293305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_293305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293305 prefixEnd_293305 := by exact prefixLift 293305
  have htrace : WordTrace (prefixWord ++ tailWord_293305) baseStart_293305 baseEnd_293305 := by
    simpa [prefixWord, tailWord_293305, baseEnd_293305] using wordTrace_append hprefix tailTrace_293305
  have hstable : (prefixWord ++ tailWord_293305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293305).length < 2 ^ (prefixWord ++ tailWord_293305).sum := by decide
  have hdescent : baseEnd_293305 < baseStart_293305 := by decide
  rcases family_descends (prefixWord ++ tailWord_293305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293321 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 2, 6]
def baseStart_293321 : Nat := 118140960795 + 293321 * 2 ^ 59
def prefixEnd_293321 : Nat := 4983230072969 + 3 ^ 40 * 293321 * 2
def baseEnd_293321 : Nat := 50204886352517371312849

theorem tailTrace_293321 : CollatzResearch.WordTrace tailWord_293321 prefixEnd_293321 50204886352517371312849 := by
  unfold tailWord_293321
  simp only [CollatzResearch.WordTrace]
  refine ⟨10698295770355587083623817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7132197180237058055749211 10698295770355587083623817)
  ·
    refine ⟨8023721827766690312717863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10698295770355587083623817 8023721827766690312717863)
    ·
      refine ⟨12035582741650035469076795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8023721827766690312717863 12035582741650035469076795)
      ·
        refine ⟨18053374112475053203615193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12035582741650035469076795 18053374112475053203615193)
        ·
          refine ⟨13540030584356289902711395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18053374112475053203615193 13540030584356289902711395)
          ·
            refine ⟨20310045876534434854067093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13540030584356289902711395 20310045876534434854067093)
            ·
              refine ⟨952033400462551633784395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20310045876534434854067093 952033400462551633784395)
              ·
                refine ⟨1428050100693827450676593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 952033400462551633784395 1428050100693827450676593)
                ·
                  refine ⟨1071037575520370588007445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1428050100693827450676593 1071037575520370588007445)
                  ·
                    refine ⟨50204886352517371312849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1071037575520370588007445 50204886352517371312849)
                    ·
                      rfl

theorem cell23_293321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 6].length) (baseStart_293321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293321 prefixEnd_293321 := by exact prefixLift 293321
  have htrace : WordTrace (prefixWord ++ tailWord_293321) baseStart_293321 baseEnd_293321 := by
    simpa [prefixWord, tailWord_293321, baseEnd_293321] using wordTrace_append hprefix tailTrace_293321
  have hstable : (prefixWord ++ tailWord_293321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293321).length < 2 ^ (prefixWord ++ tailWord_293321).sum := by decide
  have hdescent : baseEnd_293321 < baseStart_293321 := by decide
  rcases family_descends (prefixWord ++ tailWord_293321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293322 : List Nat := [3, 1, 2, 1, 2, 2, 5, 1, 2, 1, 3]
def baseStart_293322 : Nat := 118140960795 + 293322 * 2 ^ 59
def prefixEnd_293322 : Nat := 4983230072969 + 3 ^ 40 * 293322 * 2
def baseEnd_293322 : Nat := 150615172538206610026043

theorem tailTrace_293322 : CollatzResearch.WordTrace tailWord_293322 prefixEnd_293322 150615172538206610026043 := by
  unfold tailWord_293322
  simp only [CollatzResearch.WordTrace]
  refine ⟨2674583060837991063602555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7132221495567976169606813 2674583060837991063602555)
  ·
    refine ⟨4011874591256986595403833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2674583060837991063602555 4011874591256986595403833)
    ·
      refine ⟨3008905943442739946552875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4011874591256986595403833 3008905943442739946552875)
      ·
        refine ⟨4513358915164109919829313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3008905943442739946552875 4513358915164109919829313)
        ·
          refine ⟨3385019186373082439871985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4513358915164109919829313 3385019186373082439871985)
          ·
            refine ⟨2538764389779811829903989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3385019186373082439871985 2538764389779811829903989)
            ·
              refine ⟨238009161541857359053499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2538764389779811829903989 238009161541857359053499)
              ·
                refine ⟨357013742312786038580249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238009161541857359053499 357013742312786038580249)
                ·
                  refine ⟨267760306734589528935187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 357013742312786038580249 267760306734589528935187)
                  ·
                    refine ⟨401640460101884293402781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 267760306734589528935187 401640460101884293402781)
                    ·
                      refine ⟨150615172538206610026043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 401640460101884293402781 150615172538206610026043)
                      ·
                        rfl

theorem cell23_293322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_293322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293322 prefixEnd_293322 := by exact prefixLift 293322
  have htrace : WordTrace (prefixWord ++ tailWord_293322) baseStart_293322 baseEnd_293322 := by
    simpa [prefixWord, tailWord_293322, baseEnd_293322] using wordTrace_append hprefix tailTrace_293322
  have hstable : (prefixWord ++ tailWord_293322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293322).length < 2 ^ (prefixWord ++ tailWord_293322).sum := by decide
  have hdescent : baseEnd_293322 < baseStart_293322 := by decide
  rcases family_descends (prefixWord ++ tailWord_293322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293331 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 3]
def baseStart_293331 : Nat := 118140960795 + 293331 * 2 ^ 59
def prefixEnd_293331 : Nat := 4983230072969 + 3 ^ 40 * 293331 * 2
def baseEnd_293331 : Nat := 150619793864097074813501

theorem tailTrace_293331 : CollatzResearch.WordTrace tailWord_293331 prefixEnd_293331 150619793864097074813501 := by
  unfold tailWord_293331
  simp only [CollatzResearch.WordTrace]
  refine ⟨10698660500319358791487847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7132440333546239194325231 10698660500319358791487847)
  ·
    refine ⟨16047990750479038187231771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10698660500319358791487847 16047990750479038187231771)
    ·
      refine ⟨24071986125718557280847657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16047990750479038187231771 24071986125718557280847657)
      ·
        refine ⟨18053989594288917960635743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24071986125718557280847657 18053989594288917960635743)
        ·
          refine ⟨27080984391433376940953615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18053989594288917960635743 27080984391433376940953615)
          ·
            refine ⟨40621476587150065411430423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27080984391433376940953615 40621476587150065411430423)
            ·
              refine ⟨60932214880725098117145635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40621476587150065411430423 60932214880725098117145635)
              ·
                refine ⟨91398322321087647175718453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60932214880725098117145635 91398322321087647175718453)
                ·
                  refine ⟨8568592717601966922723605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91398322321087647175718453 8568592717601966922723605)
                  ·
                    refine ⟨401652783637592199502669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8568592717601966922723605 401652783637592199502669)
                    ·
                      refine ⟨150619793864097074813501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 401652783637592199502669 150619793864097074813501)
                      ·
                        rfl

theorem cell23_293331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 3].length) (baseStart_293331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293331 prefixEnd_293331 := by exact prefixLift 293331
  have htrace : WordTrace (prefixWord ++ tailWord_293331) baseStart_293331 baseEnd_293331 := by
    simpa [prefixWord, tailWord_293331, baseEnd_293331] using wordTrace_append hprefix tailTrace_293331
  have hstable : (prefixWord ++ tailWord_293331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293331).length < 2 ^ (prefixWord ++ tailWord_293331).sum := by decide
  have hdescent : baseEnd_293331 < baseStart_293331 := by decide
  rcases family_descends (prefixWord ++ tailWord_293331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293332 : List Nat := [2, 4, 1, 2, 2, 1, 1, 4, 1, 3, 2]
def baseStart_293332 : Nat := 118140960795 + 293332 * 2 ^ 59
def prefixEnd_293332 : Nat := 4983230072969 + 3 ^ 40 * 293332 * 2
def baseEnd_293332 : Nat := 150620307344751570900997

theorem tailTrace_293332 : CollatzResearch.WordTrace tailWord_293332 prefixEnd_293332 150620307344751570900997 := by
  unfold tailWord_293332
  simp only [CollatzResearch.WordTrace]
  refine ⟨5349348486657867981137125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7132464648877157308182833 5349348486657867981137125)
  ·
    refine ⟨1003002841248350246463211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5349348486657867981137125 1003002841248350246463211)
    ·
      refine ⟨1504504261872525369694817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1003002841248350246463211 1504504261872525369694817)
      ·
        refine ⟨1128378196404394027271113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1504504261872525369694817 1128378196404394027271113)
        ·
          refine ⟨846283647303295520453335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1128378196404394027271113 846283647303295520453335)
          ·
            refine ⟨1269425470954943280680003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846283647303295520453335 1269425470954943280680003)
            ·
              refine ⟨1904138206432414921020005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1269425470954943280680003 1904138206432414921020005)
              ·
                refine ⟨357025913706077797691251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1904138206432414921020005 357025913706077797691251)
                ·
                  refine ⟨535538870559116696536877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357025913706077797691251 535538870559116696536877)
                  ·
                    refine ⟨200827076459668761201329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 535538870559116696536877 200827076459668761201329)
                    ·
                      refine ⟨150620307344751570900997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 200827076459668761201329 150620307344751570900997)
                      ·
                        rfl

theorem cell23_293332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_293332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293332 prefixEnd_293332 := by exact prefixLift 293332
  have htrace : WordTrace (prefixWord ++ tailWord_293332) baseStart_293332 baseEnd_293332 := by
    simpa [prefixWord, tailWord_293332, baseEnd_293332] using wordTrace_append hprefix tailTrace_293332
  have hstable : (prefixWord ++ tailWord_293332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293332).length < 2 ^ (prefixWord ++ tailWord_293332).sum := by decide
  have hdescent : baseEnd_293332 < baseStart_293332 := by decide
  rcases family_descends (prefixWord ++ tailWord_293332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293345 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 6, 2, 2]
def baseStart_293345 : Nat := 118140960795 + 293345 * 2 ^ 59
def prefixEnd_293345 : Nat := 4983230072969 + 3 ^ 40 * 293345 * 2
def baseEnd_293345 : Nat := 150626982593260020038437

theorem tailTrace_293345 : CollatzResearch.WordTrace tailWord_293345 prefixEnd_293345 150626982593260020038437 := by
  unfold tailWord_293345
  simp only [CollatzResearch.WordTrace]
  refine ⟨10699171122268639182497489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7132780748179092788331659 10699171122268639182497489)
  ·
    refine ⟨8024378341701479386873117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10699171122268639182497489 8024378341701479386873117)
    ·
      refine ⟨3009141878138054770077419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8024378341701479386873117 3009141878138054770077419)
      ·
        refine ⟨4513712817207082155116129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3009141878138054770077419 4513712817207082155116129)
        ·
          refine ⟨3385284612905311616337097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4513712817207082155116129 3385284612905311616337097)
          ·
            refine ⟨2538963459678983712252823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3385284612905311616337097 2538963459678983712252823)
            ·
              refine ⟨3808445189518475568379235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2538963459678983712252823 3808445189518475568379235)
              ·
                refine ⟨5712667784277713352568853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3808445189518475568379235 5712667784277713352568853)
                ·
                  refine ⟨267781302388017813401665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5712667784277713352568853 267781302388017813401665)
                  ·
                    refine ⟨200835976791013360051249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 267781302388017813401665 200835976791013360051249)
                    ·
                      refine ⟨150626982593260020038437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 200835976791013360051249 150626982593260020038437)
                      ·
                        rfl

theorem cell23_293345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_293345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293345 prefixEnd_293345 := by exact prefixLift 293345
  have htrace : WordTrace (prefixWord ++ tailWord_293345) baseStart_293345 baseEnd_293345 := by
    simpa [prefixWord, tailWord_293345, baseEnd_293345] using wordTrace_append hprefix tailTrace_293345
  have hstable : (prefixWord ++ tailWord_293345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293345).length < 2 ^ (prefixWord ++ tailWord_293345).sum := by decide
  have hdescent : baseEnd_293345 < baseStart_293345 := by decide
  rcases family_descends (prefixWord ++ tailWord_293345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293361 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 1, 2, 7]
def baseStart_293361 : Nat := 118140960795 + 293361 * 2 ^ 59
def prefixEnd_293361 : Nat := 4983230072969 + 3 ^ 40 * 293361 * 2
def baseEnd_293361 : Nat := 150635198283731957438363

theorem tailTrace_293361 : CollatzResearch.WordTrace tailWord_293361 prefixEnd_293361 150635198283731957438363 := by
  unfold tailWord_293361
  simp only [CollatzResearch.WordTrace]
  refine ⟨10699754690210673915079937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7133169793473782610053291 10699754690210673915079937)
  ·
    refine ⟨8024816017658005436309953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10699754690210673915079937 8024816017658005436309953)
    ·
      refine ⟨6018612013243504077232465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8024816017658005436309953 6018612013243504077232465)
      ·
        refine ⟨4513959009932628057924349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6018612013243504077232465 4513959009932628057924349)
        ·
          refine ⟨1692734628724735521721631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4513959009932628057924349 1692734628724735521721631)
          ·
            refine ⟨2539101943087103282582447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692734628724735521721631 2539101943087103282582447)
            ·
              refine ⟨3808652914630654923873671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2539101943087103282582447 3808652914630654923873671)
              ·
                refine ⟨5712979371945982385810507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3808652914630654923873671 5712979371945982385810507)
                ·
                  refine ⟨8569469057918973578715761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5712979371945982385810507 8569469057918973578715761)
                  ·
                    refine ⟨6427101793439230184036821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8569469057918973578715761 6427101793439230184036821)
                    ·
                      refine ⟨150635198283731957438363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6427101793439230184036821 150635198283731957438363)
                      ·
                        rfl

theorem cell23_293361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_293361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293361 prefixEnd_293361 := by exact prefixLift 293361
  have htrace : WordTrace (prefixWord ++ tailWord_293361) baseStart_293361 baseEnd_293361 := by
    simpa [prefixWord, tailWord_293361, baseEnd_293361] using wordTrace_append hprefix tailTrace_293361
  have hstable : (prefixWord ++ tailWord_293361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293361).length < 2 ^ (prefixWord ++ tailWord_293361).sum := by decide
  have hdescent : baseEnd_293361 < baseStart_293361 := by decide
  rcases family_descends (prefixWord ++ tailWord_293361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293381 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 3, 7]
def baseStart_293381 : Nat := 118140960795 + 293381 * 2 ^ 59
def prefixEnd_293381 : Nat := 4983230072969 + 3 ^ 40 * 293381 * 2
def baseEnd_293381 : Nat := 50215155965607293062757

theorem tailTrace_293381 : CollatzResearch.WordTrace tailWord_293381 prefixEnd_293381 50215155965607293062757 := by
  unfold tailWord_293381
  simp only [CollatzResearch.WordTrace]
  refine ⟨10700484150138217330807997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7133656100092144887205331 10700484150138217330807997)
  ·
    refine ⟨4012681556301831499052999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10700484150138217330807997 4012681556301831499052999)
    ·
      refine ⟨6019022334452747248579499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4012681556301831499052999 6019022334452747248579499)
      ·
        refine ⟨9028533501679120872869249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6019022334452747248579499 9028533501679120872869249)
        ·
          refine ⟨6771400126259340654651937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9028533501679120872869249 6771400126259340654651937)
          ·
            refine ⟨5078550094694505490988953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6771400126259340654651937 5078550094694505490988953)
            ·
              refine ⟨3808912571020879118241715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5078550094694505490988953 3808912571020879118241715)
              ·
                refine ⟨5713368856531318677362573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3808912571020879118241715 5713368856531318677362573)
                ·
                  refine ⟨2142513321199244504010965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5713368856531318677362573 2142513321199244504010965)
                  ·
                    refine ⟨50215155965607293062757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2142513321199244504010965 50215155965607293062757)
                    ·
                      rfl

theorem cell23_293381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_293381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293381 prefixEnd_293381 := by exact prefixLift 293381
  have htrace : WordTrace (prefixWord ++ tailWord_293381) baseStart_293381 baseEnd_293381 := by
    simpa [prefixWord, tailWord_293381, baseEnd_293381] using wordTrace_append hprefix tailTrace_293381
  have hstable : (prefixWord ++ tailWord_293381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293381).length < 2 ^ (prefixWord ++ tailWord_293381).sum := by decide
  have hdescent : baseEnd_293381 < baseStart_293381 := by decide
  rcases family_descends (prefixWord ++ tailWord_293381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293391 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 5]
def baseStart_293391 : Nat := 118140960795 + 293391 * 2 ^ 59
def prefixEnd_293391 : Nat := 4983230072969 + 3 ^ 40 * 293391 * 2
def baseEnd_293391 : Nat := 150650602703366840063225

theorem tailTrace_293391 : CollatzResearch.WordTrace tailWord_293391 prefixEnd_293391 150650602703366840063225 := by
  unfold tailWord_293391
  simp only [CollatzResearch.WordTrace]
  refine ⟨10700848880101989038672027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7133899253401326025781351 10700848880101989038672027)
  ·
    refine ⟨16051273320152983558008041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10700848880101989038672027 16051273320152983558008041)
    ·
      refine ⟨12038454990114737668506031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16051273320152983558008041 12038454990114737668506031)
      ·
        refine ⟨18057682485172106502759047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12038454990114737668506031 18057682485172106502759047)
        ·
          refine ⟨27086523727758159754138571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18057682485172106502759047 27086523727758159754138571)
          ·
            refine ⟨40629785591637239631207857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27086523727758159754138571 40629785591637239631207857)
            ·
              refine ⟨30472339193727929723405893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40629785591637239631207857 30472339193727929723405893)
              ·
                refine ⟨5713563598823986823138605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30472339193727929723405893 5713563598823986823138605)
                ·
                  refine ⟨2142586349558995058676977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5713563598823986823138605 2142586349558995058676977)
                  ·
                    refine ⟨1606939762169246294007733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2142586349558995058676977 1606939762169246294007733)
                    ·
                      refine ⟨150650602703366840063225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1606939762169246294007733 150650602703366840063225)
                      ·
                        rfl

theorem cell23_293391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_293391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293391 prefixEnd_293391 := by exact prefixLift 293391
  have htrace : WordTrace (prefixWord ++ tailWord_293391) baseStart_293391 baseEnd_293391 := by
    simpa [prefixWord, tailWord_293391, baseEnd_293391] using wordTrace_append hprefix tailTrace_293391
  have hstable : (prefixWord ++ tailWord_293391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293391).length < 2 ^ (prefixWord ++ tailWord_293391).sum := by decide
  have hdescent : baseEnd_293391 < baseStart_293391 := by decide
  rcases family_descends (prefixWord ++ tailWord_293391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293445 : List Nat := [1, 3, 1, 1, 1, 6, 1, 2, 3, 4]
def baseStart_293445 : Nat := 118140960795 + 293445 * 2 ^ 59
def prefixEnd_293445 : Nat := 4983230072969 + 3 ^ 40 * 293445 * 2
def baseEnd_293445 : Nat := 50226110219569876262659

theorem tailTrace_293445 : CollatzResearch.WordTrace tailWord_293445 prefixEnd_293445 50226110219569876262659 := by
  unfold tailWord_293445
  simp only [CollatzResearch.WordTrace]
  refine ⟨10702818421906356261137789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7135212281270904174091859 10702818421906356261137789)
  ·
    refine ⟨4013556908214883597926671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10702818421906356261137789 4013556908214883597926671)
    ·
      refine ⟨6020335362322325396890007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4013556908214883597926671 6020335362322325396890007)
      ·
        refine ⟨9030503043483488095335011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6020335362322325396890007 9030503043483488095335011)
        ·
          refine ⟨13545754565225232143002517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9030503043483488095335011 13545754565225232143002517)
          ·
            refine ⟨634957245244932756703243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13545754565225232143002517 634957245244932756703243)
            ·
              refine ⟨952435867867399135054865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634957245244932756703243 952435867867399135054865)
              ·
                refine ⟨714326900900549351291149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952435867867399135054865 714326900900549351291149)
                ·
                  refine ⟨267872587837706006734181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 714326900900549351291149 267872587837706006734181)
                  ·
                    refine ⟨50226110219569876262659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 267872587837706006734181 50226110219569876262659)
                    ·
                      rfl

theorem cell23_293445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_293445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293445 prefixEnd_293445 := by exact prefixLift 293445
  have htrace : WordTrace (prefixWord ++ tailWord_293445) baseStart_293445 baseEnd_293445 := by
    simpa [prefixWord, tailWord_293445, baseEnd_293445] using wordTrace_append hprefix tailTrace_293445
  have hstable : (prefixWord ++ tailWord_293445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293445).length < 2 ^ (prefixWord ++ tailWord_293445).sum := by decide
  have hdescent : baseEnd_293445 < baseStart_293445 := by decide
  rcases family_descends (prefixWord ++ tailWord_293445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293455 : List Nat := [1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 3]
def baseStart_293455 : Nat := 118140960795 + 293455 * 2 ^ 59
def prefixEnd_293455 : Nat := 4983230072969 + 3 ^ 40 * 293455 * 2
def baseEnd_293455 : Nat := 150683465465254589662931

theorem tailTrace_293455 : CollatzResearch.WordTrace tailWord_293455 prefixEnd_293455 150683465465254589662931 := by
  unfold tailWord_293455
  simp only [CollatzResearch.WordTrace]
  refine ⟨10703183151870127969001819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7135455434580085312667879 10703183151870127969001819)
  ·
    refine ⟨16054774727805191953502729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10703183151870127969001819 16054774727805191953502729)
    ·
      refine ⟨12041081045853893965127047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16054774727805191953502729 12041081045853893965127047)
      ·
        refine ⟨18061621568780840947690571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12041081045853893965127047 18061621568780840947690571)
        ·
          refine ⟨27092432353171261421535857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18061621568780840947690571 27092432353171261421535857)
          ·
            refine ⟨20319324264878446066151893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27092432353171261421535857 20319324264878446066151893)
            ·
              refine ⟨476234162458088579675435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 20319324264878446066151893 476234162458088579675435)
              ·
                refine ⟨714351243687132869513153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476234162458088579675435 714351243687132869513153)
                ·
                  refine ⟨535763432765349652134865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 714351243687132869513153 535763432765349652134865)
                  ·
                    refine ⟨401822574574012239101149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 535763432765349652134865 401822574574012239101149)
                    ·
                      refine ⟨150683465465254589662931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 401822574574012239101149 150683465465254589662931)
                      ·
                        rfl

theorem cell23_293455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 3].length) (baseStart_293455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293455 prefixEnd_293455 := by exact prefixLift 293455
  have htrace : WordTrace (prefixWord ++ tailWord_293455) baseStart_293455 baseEnd_293455 := by
    simpa [prefixWord, tailWord_293455, baseEnd_293455] using wordTrace_append hprefix tailTrace_293455
  have hstable : (prefixWord ++ tailWord_293455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293455).length < 2 ^ (prefixWord ++ tailWord_293455).sum := by decide
  have hdescent : baseEnd_293455 < baseStart_293455 := by decide
  rcases family_descends (prefixWord ++ tailWord_293455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293458 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 8]
def baseStart_293458 : Nat := 118140960795 + 293458 * 2 ^ 59
def prefixEnd_293458 : Nat := 4983230072969 + 3 ^ 40 * 293458 * 2
def baseEnd_293458 : Nat := 16742778434135341991713

theorem tailTrace_293458 : CollatzResearch.WordTrace tailWord_293458 prefixEnd_293458 16742778434135341991713 := by
  unfold tailWord_293458
  simp only [CollatzResearch.WordTrace]
  refine ⟨2675823142714814870340257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7135528380572839654240685 2675823142714814870340257)
  ·
    refine ⟨2006867357036111152755193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2675823142714814870340257 2006867357036111152755193)
    ·
      refine ⟨1505150517777083364566395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2006867357036111152755193 1505150517777083364566395)
      ·
        refine ⟨2257725776665625046849593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1505150517777083364566395 2257725776665625046849593)
        ·
          refine ⟨1693294332499218785137195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2257725776665625046849593 1693294332499218785137195)
          ·
            refine ⟨2539941498748828177705793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693294332499218785137195 2539941498748828177705793)
            ·
              refine ⟨1904956124061621133279345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2539941498748828177705793 1904956124061621133279345)
              ·
                refine ⟨1428717093046215849959509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1904956124061621133279345 1428717093046215849959509)
                ·
                  refine ⟨16742778434135341991713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1428717093046215849959509 16742778434135341991713)
                  ·
                    rfl

theorem cell23_293458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_293458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293458 prefixEnd_293458 := by exact prefixLift 293458
  have htrace : WordTrace (prefixWord ++ tailWord_293458) baseStart_293458 baseEnd_293458 := by
    simpa [prefixWord, tailWord_293458, baseEnd_293458] using wordTrace_append hprefix tailTrace_293458
  have hstable : (prefixWord ++ tailWord_293458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293458).length < 2 ^ (prefixWord ++ tailWord_293458).sum := by decide
  have hdescent : baseEnd_293458 < baseStart_293458 := by decide
  rcases family_descends (prefixWord ++ tailWord_293458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293495 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 1, 5, 2]
def baseStart_293495 : Nat := 118140960795 + 293495 * 2 ^ 59
def prefixEnd_293495 : Nat := 4983230072969 + 3 ^ 40 * 293495 * 2
def baseEnd_293495 : Nat := 150704004691434433162747

theorem tailTrace_293495 : CollatzResearch.WordTrace tailWord_293495 prefixEnd_293495 150704004691434433162747 := by
  unfold tailWord_293495
  simp only [CollatzResearch.WordTrace]
  refine ⟨10704642071725214800457939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7136428047816809866971959 10704642071725214800457939)
  ·
    refine ⟨16056963107587822200686909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10704642071725214800457939 16056963107587822200686909)
    ·
      refine ⟨6021361165345433325257591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16056963107587822200686909 6021361165345433325257591)
      ·
        refine ⟨9032041748018149987886387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6021361165345433325257591 9032041748018149987886387)
        ·
          refine ⟨13548062622027224981829581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9032041748018149987886387 13548062622027224981829581)
          ·
            refine ⟨5080523483260209368186093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13548062622027224981829581 5080523483260209368186093)
            ·
              refine ⟨1905196306222578513069785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5080523483260209368186093 1905196306222578513069785)
              ·
                refine ⟨1428897229666933884802339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1905196306222578513069785 1428897229666933884802339)
                ·
                  refine ⟨2143345844500400827203509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1428897229666933884802339 2143345844500400827203509)
                  ·
                    refine ⟨200938672921912577550329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2143345844500400827203509 200938672921912577550329)
                    ·
                      refine ⟨150704004691434433162747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 200938672921912577550329 150704004691434433162747)
                      ·
                        rfl

theorem cell23_293495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 5, 2].length) (baseStart_293495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293495 prefixEnd_293495 := by exact prefixLift 293495
  have htrace : WordTrace (prefixWord ++ tailWord_293495) baseStart_293495 baseEnd_293495 := by
    simpa [prefixWord, tailWord_293495, baseEnd_293495] using wordTrace_append hprefix tailTrace_293495
  have hstable : (prefixWord ++ tailWord_293495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293495).length < 2 ^ (prefixWord ++ tailWord_293495).sum := by decide
  have hdescent : baseEnd_293495 < baseStart_293495 := by decide
  rcases family_descends (prefixWord ++ tailWord_293495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293522 : List Nat := [3, 2, 3, 1, 2, 1, 2, 3, 1, 5]
def baseStart_293522 : Nat := 118140960795 + 293522 * 2 ^ 59
def prefixEnd_293522 : Nat := 4983230072969 + 3 ^ 40 * 293522 * 2
def baseEnd_293522 : Nat := 50239289556368609175041

theorem tailTrace_293522 : CollatzResearch.WordTrace tailWord_293522 prefixEnd_293522 50239289556368609175041 := by
  unfold tailWord_293522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2676406710656849602922705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7137084561751598941127213 2676406710656849602922705)
  ·
    refine ⟨2007305032992637202192029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2676406710656849602922705 2007305032992637202192029)
    ·
      refine ⟨752739387372238950822011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2007305032992637202192029 752739387372238950822011)
      ·
        refine ⟨1129109081058358426233017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 752739387372238950822011 1129109081058358426233017)
        ·
          refine ⟨846831810793768819674763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1129109081058358426233017 846831810793768819674763)
          ·
            refine ⟨1270247716190653229512145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846831810793768819674763 1270247716190653229512145)
            ·
              refine ⟨952685787142989922134109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1270247716190653229512145 952685787142989922134109)
              ·
                refine ⟨357257170178621220800291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 952685787142989922134109 357257170178621220800291)
                ·
                  refine ⟨535885755267931831200437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357257170178621220800291 535885755267931831200437)
                  ·
                    refine ⟨50239289556368609175041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 535885755267931831200437 50239289556368609175041)
                    ·
                      rfl

theorem cell23_293522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_293522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293522 prefixEnd_293522 := by exact prefixLift 293522
  have htrace : WordTrace (prefixWord ++ tailWord_293522) baseStart_293522 baseEnd_293522 := by
    simpa [prefixWord, tailWord_293522, baseEnd_293522] using wordTrace_append hprefix tailTrace_293522
  have hstable : (prefixWord ++ tailWord_293522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293522).length < 2 ^ (prefixWord ++ tailWord_293522).sum := by decide
  have hdescent : baseEnd_293522 < baseStart_293522 := by decide
  rcases family_descends (prefixWord ++ tailWord_293522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293536 : List Nat := [2, 1, 1, 4, 5, 1, 1, 1, 3, 1, 3]
def baseStart_293536 : Nat := 118140960795 + 293536 * 2 ^ 59
def prefixEnd_293536 : Nat := 4983230072969 + 3 ^ 40 * 293536 * 2
def baseEnd_293536 : Nat := 150725057398268772750059

theorem tailTrace_293536 : CollatzResearch.WordTrace tailWord_293536 prefixEnd_293536 150725057398268772750059 := by
  unfold tailWord_293536
  simp only [CollatzResearch.WordTrace]
  refine ⟨5353068732288339401350231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7137424976384452535133641 5353068732288339401350231)
  ·
    refine ⟨8029603098432509102025347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5353068732288339401350231 8029603098432509102025347)
    ·
      refine ⟨12044404647648763653038021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8029603098432509102025347 12044404647648763653038021)
      ·
        refine ⟨2258325871434143184944629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12044404647648763653038021 2258325871434143184944629)
        ·
          refine ⟨211718050446950923588559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2258325871434143184944629 211718050446950923588559)
          ·
            refine ⟨317577075670426385382839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211718050446950923588559 317577075670426385382839)
            ·
              refine ⟨476365613505639578074259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317577075670426385382839 476365613505639578074259)
              ·
                refine ⟨714548420258459367111389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476365613505639578074259 714548420258459367111389)
                ·
                  refine ⟨267955657596922262666771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 714548420258459367111389 267955657596922262666771)
                  ·
                    refine ⟨401933486395383394000157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 267955657596922262666771 401933486395383394000157)
                    ·
                      refine ⟨150725057398268772750059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 401933486395383394000157 150725057398268772750059)
                      ·
                        rfl

theorem cell23_293536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_293536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293536 prefixEnd_293536 := by exact prefixLift 293536
  have htrace : WordTrace (prefixWord ++ tailWord_293536) baseStart_293536 baseEnd_293536 := by
    simpa [prefixWord, tailWord_293536, baseEnd_293536] using wordTrace_append hprefix tailTrace_293536
  have hstable : (prefixWord ++ tailWord_293536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293536).length < 2 ^ (prefixWord ++ tailWord_293536).sum := by decide
  have hdescent : baseEnd_293536 < baseStart_293536 := by decide
  rcases family_descends (prefixWord ++ tailWord_293536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293559 : List Nat := [1, 1, 3, 1, 6, 2, 1, 2, 1, 1, 4]
def baseStart_293559 : Nat := 118140960795 + 293559 * 2 ^ 59
def prefixEnd_293559 : Nat := 4983230072969 + 3 ^ 40 * 293559 * 2
def baseEnd_293559 : Nat := 150736867453322182762453

theorem tailTrace_293559 : CollatzResearch.WordTrace tailWord_293559 prefixEnd_293559 150736867453322182762453 := by
  unfold tailWord_293559
  simp only [CollatzResearch.WordTrace]
  refine ⟨10706976343493353730787731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7137984228995569153858487 10706976343493353730787731)
  ·
    refine ⟨16060464515240030596181597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10706976343493353730787731 16060464515240030596181597)
    ·
      refine ⟨6022674193215011473568099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16060464515240030596181597 6022674193215011473568099)
      ·
        refine ⟨9034011289822517210352149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6022674193215011473568099 9034011289822517210352149)
        ·
          refine ⟨423469279210430494235257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9034011289822517210352149 423469279210430494235257)
          ·
            refine ⟨317601959407822870676443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 423469279210430494235257 317601959407822870676443)
            ·
              refine ⟨476402939111734306014665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317601959407822870676443 476402939111734306014665)
              ·
                refine ⟨357302204333800729510999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476402939111734306014665 357302204333800729510999)
                ·
                  refine ⟨535953306500701094266499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357302204333800729510999 535953306500701094266499)
                  ·
                    refine ⟨803929959751051641399749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 535953306500701094266499 803929959751051641399749)
                    ·
                      refine ⟨150736867453322182762453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 803929959751051641399749 150736867453322182762453)
                      ·
                        rfl

theorem cell23_293559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 1, 4].length) (baseStart_293559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293559 prefixEnd_293559 := by exact prefixLift 293559
  have htrace : WordTrace (prefixWord ++ tailWord_293559) baseStart_293559 baseEnd_293559 := by
    simpa [prefixWord, tailWord_293559, baseEnd_293559] using wordTrace_append hprefix tailTrace_293559
  have hstable : (prefixWord ++ tailWord_293559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293559).length < 2 ^ (prefixWord ++ tailWord_293559).sum := by decide
  have hdescent : baseEnd_293559 < baseStart_293559 := by decide
  rcases family_descends (prefixWord ++ tailWord_293559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293569 : List Nat := [1, 2, 6, 2, 1, 1, 1, 2, 1, 6]
def baseStart_293569 : Nat := 118140960795 + 293569 * 2 ^ 59
def prefixEnd_293569 : Nat := 4983230072969 + 3 ^ 40 * 293569 * 2
def baseEnd_293569 : Nat := 50247334086622381212469

theorem tailTrace_293569 : CollatzResearch.WordTrace tailWord_293569 prefixEnd_293569 50247334086622381212469 := by
  unfold tailWord_293569
  simp only [CollatzResearch.WordTrace]
  refine ⟨10707341073457125438651761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7138227382304750292434507 10707341073457125438651761)
  ·
    refine ⟨8030505805092844078988821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10707341073457125438651761 8030505805092844078988821)
    ·
      refine ⟨376429959613727066202601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8030505805092844078988821 376429959613727066202601)
      ·
        refine ⟨282322469710295299651951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376429959613727066202601 282322469710295299651951)
        ·
          refine ⟨423483704565442949477927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282322469710295299651951 423483704565442949477927)
          ·
            refine ⟨635225556848164424216891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423483704565442949477927 635225556848164424216891)
            ·
              refine ⟨952838335272246636325337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635225556848164424216891 952838335272246636325337)
              ·
                refine ⟨714628751454184977244003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952838335272246636325337 714628751454184977244003)
                ·
                  refine ⟨1071943127181277465866005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714628751454184977244003 1071943127181277465866005)
                  ·
                    refine ⟨50247334086622381212469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1071943127181277465866005 50247334086622381212469)
                    ·
                      rfl

theorem cell23_293569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_293569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293569 prefixEnd_293569 := by exact prefixLift 293569
  have htrace : WordTrace (prefixWord ++ tailWord_293569) baseStart_293569 baseEnd_293569 := by
    simpa [prefixWord, tailWord_293569, baseEnd_293569] using wordTrace_append hprefix tailTrace_293569
  have hstable : (prefixWord ++ tailWord_293569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293569).length < 2 ^ (prefixWord ++ tailWord_293569).sum := by decide
  have hdescent : baseEnd_293569 < baseStart_293569 := by decide
  rcases family_descends (prefixWord ++ tailWord_293569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293572 : List Nat := [2, 3, 3, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_293572 : Nat := 118140960795 + 293572 * 2 ^ 59
def prefixEnd_293572 : Nat := 4983230072969 + 3 ^ 40 * 293572 * 2
def baseEnd_293572 : Nat := 150743542701830631899893

theorem tailTrace_293572 : CollatzResearch.WordTrace tailWord_293572 prefixEnd_293572 150743542701830631899893 := by
  unfold tailWord_293572
  simp only [CollatzResearch.WordTrace]
  refine ⟨5353725246223128475505485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7138300328297504634007313 5353725246223128475505485)
  ·
    refine ⟨2007646967333673178314557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5353725246223128475505485 2007646967333673178314557)
    ·
      refine ⟨752867612750127441867959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2007646967333673178314557 752867612750127441867959)
      ·
        refine ⟨1129301419125191162801939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 752867612750127441867959 1129301419125191162801939)
        ·
          refine ⟨1693952128687786744202909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1129301419125191162801939 1693952128687786744202909)
          ·
            refine ⟨635232048257920029076091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1693952128687786744202909 635232048257920029076091)
            ·
              refine ⟨952848072386880043614137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635232048257920029076091 952848072386880043614137)
              ·
                refine ⟨714636054290160032710603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952848072386880043614137 714636054290160032710603)
                ·
                  refine ⟨1071954081435240049065905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714636054290160032710603 1071954081435240049065905)
                  ·
                    refine ⟨803965561076430036799429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1071954081435240049065905 803965561076430036799429)
                    ·
                      refine ⟨150743542701830631899893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 803965561076430036799429 150743542701830631899893)
                      ·
                        rfl

theorem cell23_293572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_293572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293572 prefixEnd_293572 := by exact prefixLift 293572
  have htrace : WordTrace (prefixWord ++ tailWord_293572) baseStart_293572 baseEnd_293572 := by
    simpa [prefixWord, tailWord_293572, baseEnd_293572] using wordTrace_append hprefix tailTrace_293572
  have hstable : (prefixWord ++ tailWord_293572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293572).length < 2 ^ (prefixWord ++ tailWord_293572).sum := by decide
  have hdescent : baseEnd_293572 < baseStart_293572 := by decide
  rcases family_descends (prefixWord ++ tailWord_293572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293666 : List Nat := [3, 3, 1, 1, 2, 4, 1, 1, 1, 4, 2]
def baseStart_293666 : Nat := 118140960795 + 293666 * 2 ^ 59
def prefixEnd_293666 : Nat := 4983230072969 + 3 ^ 40 * 293666 * 2
def baseEnd_293666 : Nat := 150791809883353264124461

theorem tailTrace_293666 : CollatzResearch.WordTrace tailWord_293666 prefixEnd_293666 150791809883353264124461 := by
  unfold tailWord_293666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2677719738526427751233213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7140585969403807336621901 2677719738526427751233213)
  ·
    refine ⟨1004144901947410406712455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2677719738526427751233213 1004144901947410406712455)
    ·
      refine ⟨1506217352921115610068683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1004144901947410406712455 1506217352921115610068683)
      ·
        refine ⟨2259326029381673415103025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1506217352921115610068683 2259326029381673415103025)
        ·
          refine ⟨1694494522036255061327269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2259326029381673415103025 1694494522036255061327269)
          ·
            refine ⟨317717722881797823998863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1694494522036255061327269 317717722881797823998863)
            ·
              refine ⟨476576584322696735998295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317717722881797823998863 476576584322696735998295)
              ·
                refine ⟨714864876484045103997443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476576584322696735998295 714864876484045103997443)
                ·
                  refine ⟨1072297314726067655996165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714864876484045103997443 1072297314726067655996165)
                  ·
                    refine ⟨201055746511137685499281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1072297314726067655996165 201055746511137685499281)
                    ·
                      refine ⟨150791809883353264124461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 201055746511137685499281 150791809883353264124461)
                      ·
                        rfl

theorem cell23_293666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_293666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293666 prefixEnd_293666 := by exact prefixLift 293666
  have htrace : WordTrace (prefixWord ++ tailWord_293666) baseStart_293666 baseEnd_293666 := by
    simpa [prefixWord, tailWord_293666, baseEnd_293666] using wordTrace_append hprefix tailTrace_293666
  have hstable : (prefixWord ++ tailWord_293666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293666).length < 2 ^ (prefixWord ++ tailWord_293666).sum := by decide
  have hdescent : baseEnd_293666 < baseStart_293666 := by decide
  rcases family_descends (prefixWord ++ tailWord_293666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293692 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 1, 7, 2]
def baseStart_293692 : Nat := 118140960795 + 293692 * 2 ^ 59
def prefixEnd_293692 : Nat := 4983230072969 + 3 ^ 40 * 293692 * 2
def baseEnd_293692 : Nat := 150805160380370162399341

theorem tailTrace_293692 : CollatzResearch.WordTrace tailWord_293692 prefixEnd_293692 150805160380370162399341 := by
  unfold tailWord_293692
  simp only [CollatzResearch.WordTrace]
  refine ⟨5355913626005758722689665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7141218168007678296919553 5355913626005758722689665)
  ·
    refine ⟨4016935219504319042017249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5355913626005758722689665 4016935219504319042017249)
    ·
      refine ⟨3012701414628239281512937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4016935219504319042017249 3012701414628239281512937)
      ·
        refine ⟨2259526060971179461134703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3012701414628239281512937 2259526060971179461134703)
        ·
          refine ⟨3389289091456769191702055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2259526060971179461134703 3389289091456769191702055)
          ·
            refine ⟨5083933637185153787553083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3389289091456769191702055 5083933637185153787553083)
            ·
              refine ⟨7625900455777730681329625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5083933637185153787553083 7625900455777730681329625)
              ·
                refine ⟨5719425341833298010997219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7625900455777730681329625 5719425341833298010997219)
                ·
                  refine ⟨8579138012749947016495829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5719425341833298010997219 8579138012749947016495829)
                  ·
                    refine ⟨201073547173826883199121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8579138012749947016495829 201073547173826883199121)
                    ·
                      refine ⟨150805160380370162399341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 201073547173826883199121 150805160380370162399341)
                      ·
                        rfl

theorem cell23_293692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_293692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293692 prefixEnd_293692 := by exact prefixLift 293692
  have htrace : WordTrace (prefixWord ++ tailWord_293692) baseStart_293692 baseEnd_293692 := by
    simpa [prefixWord, tailWord_293692, baseEnd_293692] using wordTrace_append hprefix tailTrace_293692
  have hstable : (prefixWord ++ tailWord_293692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293692).length < 2 ^ (prefixWord ++ tailWord_293692).sum := by decide
  have hdescent : baseEnd_293692 < baseStart_293692 := by decide
  rcases family_descends (prefixWord ++ tailWord_293692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293785 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 7]
def baseStart_293785 : Nat := 118140960795 + 293785 * 2 ^ 59
def prefixEnd_293785 : Nat := 4983230072969 + 3 ^ 40 * 293785 * 2
def baseEnd_293785 : Nat := 150852914081238298536413

theorem tailTrace_293785 : CollatzResearch.WordTrace tailWord_293785 prefixEnd_293785 150852914081238298536413 := by
  unfold tailWord_293785
  simp only [CollatzResearch.WordTrace]
  refine ⟨10715219240674594328514809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7143479493783062885676539 10715219240674594328514809)
  ·
    refine ⟨8036414430505945746386107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10715219240674594328514809 8036414430505945746386107)
    ·
      refine ⟨12054621645758918619579161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8036414430505945746386107 12054621645758918619579161)
      ·
        refine ⟨9040966234319188964684371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12054621645758918619579161 9040966234319188964684371)
        ·
          refine ⟨13561449351478783447026557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9040966234319188964684371 13561449351478783447026557)
          ·
            refine ⟨5085543506804543792634959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13561449351478783447026557 5085543506804543792634959)
            ·
              refine ⟨7628315260206815688952439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5085543506804543792634959 7628315260206815688952439)
              ·
                refine ⟨11442472890310223533428659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7628315260206815688952439 11442472890310223533428659)
                ·
                  refine ⟨17163709335465335300142989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11442472890310223533428659 17163709335465335300142989)
                  ·
                    refine ⟨6436391000799500737553621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17163709335465335300142989 6436391000799500737553621)
                    ·
                      refine ⟨150852914081238298536413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6436391000799500737553621 150852914081238298536413)
                      ·
                        rfl

theorem cell23_293785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_293785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293785 prefixEnd_293785 := by exact prefixLift 293785
  have htrace : WordTrace (prefixWord ++ tailWord_293785) baseStart_293785 baseEnd_293785 := by
    simpa [prefixWord, tailWord_293785, baseEnd_293785] using wordTrace_append hprefix tailTrace_293785
  have hstable : (prefixWord ++ tailWord_293785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293785).length < 2 ^ (prefixWord ++ tailWord_293785).sum := by decide
  have hdescent : baseEnd_293785 < baseStart_293785 := by decide
  rcases family_descends (prefixWord ++ tailWord_293785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293792 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 3, 5]
def baseStart_293792 : Nat := 118140960795 + 293792 * 2 ^ 59
def prefixEnd_293792 : Nat := 4983230072969 + 3 ^ 40 * 293792 * 2
def baseEnd_293792 : Nat := 50285502815273257049627

theorem tailTrace_293792 : CollatzResearch.WordTrace tailWord_293792 prefixEnd_293792 50285502815273257049627 := by
  unfold tailWord_293792
  simp only [CollatzResearch.WordTrace]
  refine ⟨5357737275824617262009815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7143649701099489682679753 5357737275824617262009815)
  ·
    refine ⟨8036605913736925893014723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5357737275824617262009815 8036605913736925893014723)
    ·
      refine ⟨12054908870605388839522085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8036605913736925893014723 12054908870605388839522085)
      ·
        refine ⟨2260295413238510407410391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12054908870605388839522085 2260295413238510407410391)
        ·
          refine ⟨3390443119857765611115587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2260295413238510407410391 3390443119857765611115587)
          ·
            refine ⟨5085664679786648416673381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3390443119857765611115587 5085664679786648416673381)
            ·
              refine ⟨953562127459996578126259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5085664679786648416673381 953562127459996578126259)
              ·
                refine ⟨1430343191189994867189389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 953562127459996578126259 1430343191189994867189389)
                ·
                  refine ⟨536378696696248075196021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1430343191189994867189389 536378696696248075196021)
                  ·
                    refine ⟨50285502815273257049627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 536378696696248075196021 50285502815273257049627)
                    ·
                      rfl

theorem cell23_293792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 3, 5].length) (baseStart_293792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293792 prefixEnd_293792 := by exact prefixLift 293792
  have htrace : WordTrace (prefixWord ++ tailWord_293792) baseStart_293792 baseEnd_293792 := by
    simpa [prefixWord, tailWord_293792, baseEnd_293792] using wordTrace_append hprefix tailTrace_293792
  have hstable : (prefixWord ++ tailWord_293792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293792).length < 2 ^ (prefixWord ++ tailWord_293792).sum := by decide
  have hdescent : baseEnd_293792 < baseStart_293792 := by decide
  rcases family_descends (prefixWord ++ tailWord_293792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293839 : List Nat := [1, 1, 2, 1, 1, 8, 1, 1, 1, 6]
def baseStart_293839 : Nat := 118140960795 + 293839 * 2 ^ 59
def prefixEnd_293839 : Nat := 4983230072969 + 3 ^ 40 * 293839 * 2
def baseEnd_293839 : Nat := 50293547345527029087055

theorem tailTrace_293839 : CollatzResearch.WordTrace tailWord_293839 prefixEnd_293839 50293547345527029087055 := by
  unfold tailWord_293839
  simp only [CollatzResearch.WordTrace]
  refine ⟨10717188782478961550980571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7144792521652641033987047 10717188782478961550980571)
  ·
    refine ⟨16075783173718442326470857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10717188782478961550980571 16075783173718442326470857)
    ·
      refine ⟨12056837380288831744853143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16075783173718442326470857 12056837380288831744853143)
      ·
        refine ⟨18085256070433247617279715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12056837380288831744853143 18085256070433247617279715)
        ·
          refine ⟨27127884105649871425919573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18085256070433247617279715 27127884105649871425919573)
          ·
            refine ⟨317904891863084430772495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 27127884105649871425919573 317904891863084430772495)
            ·
              refine ⟨476857337794626646158743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317904891863084430772495 476857337794626646158743)
              ·
                refine ⟨715286006691939969238115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476857337794626646158743 715286006691939969238115)
                ·
                  refine ⟨1072929010037909953857173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 715286006691939969238115 1072929010037909953857173)
                  ·
                    refine ⟨50293547345527029087055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1072929010037909953857173 50293547345527029087055)
                    ·
                      rfl

theorem cell23_293839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 6].length) (baseStart_293839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293839 prefixEnd_293839 := by exact prefixLift 293839
  have htrace : WordTrace (prefixWord ++ tailWord_293839) baseStart_293839 baseEnd_293839 := by
    simpa [prefixWord, tailWord_293839, baseEnd_293839] using wordTrace_append hprefix tailTrace_293839
  have hstable : (prefixWord ++ tailWord_293839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293839).length < 2 ^ (prefixWord ++ tailWord_293839).sum := by decide
  have hdescent : baseEnd_293839 < baseStart_293839 := by decide
  rcases family_descends (prefixWord ++ tailWord_293839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293866 : List Nat := [3, 1, 3, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_293866 : Nat := 118140960795 + 293866 * 2 ^ 59
def prefixEnd_293866 : Nat := 4983230072969 + 3 ^ 40 * 293866 * 2
def baseEnd_293866 : Nat := 150894506014252481623541

theorem tailTrace_293866 : CollatzResearch.WordTrace tailWord_293866 prefixEnd_293866 150894506014252481623541 := by
  unfold tailWord_293866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2679543388345286290553363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7145449035587430108142301 2679543388345286290553363)
  ·
    refine ⟨4019315082517929435830045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2679543388345286290553363 4019315082517929435830045)
    ·
      refine ⟨1507243155944223538436267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4019315082517929435830045 1507243155944223538436267)
      ·
        refine ⟨2260864733916335307654401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1507243155944223538436267 2260864733916335307654401)
        ·
          refine ⟨1695648550437251480740801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2260864733916335307654401 1695648550437251480740801)
          ·
            refine ⟨1271736412827938610555601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1695648550437251480740801 1271736412827938610555601)
            ·
              refine ⟨953802309620953957916701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1271736412827938610555601 953802309620953957916701)
              ·
                refine ⟨357675866107857734218763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 953802309620953957916701 357675866107857734218763)
                ·
                  refine ⟨536513799161786601328145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357675866107857734218763 536513799161786601328145)
                  ·
                    refine ⟨402385349371339950996109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 536513799161786601328145 402385349371339950996109)
                    ·
                      refine ⟨150894506014252481623541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 402385349371339950996109 150894506014252481623541)
                      ·
                        rfl

theorem cell23_293866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_293866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293866 prefixEnd_293866 := by exact prefixLift 293866
  have htrace : WordTrace (prefixWord ++ tailWord_293866) baseStart_293866 baseEnd_293866 := by
    simpa [prefixWord, tailWord_293866, baseEnd_293866] using wordTrace_append hprefix tailTrace_293866
  have hstable : (prefixWord ++ tailWord_293866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293866).length < 2 ^ (prefixWord ++ tailWord_293866).sum := by decide
  have hdescent : baseEnd_293866 < baseStart_293866 := by decide
  rcases family_descends (prefixWord ++ tailWord_293866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293886 : List Nat := [4, 2, 2, 2, 2, 1, 2, 8]
def baseStart_293886 : Nat := 118140960795 + 293886 * 2 ^ 59
def prefixEnd_293886 : Nat := 4983230072969 + 3 ^ 40 * 293886 * 2
def baseEnd_293886 : Nat := 5589065763975644569387

theorem tailTrace_293886 : CollatzResearch.WordTrace tailWord_293886 prefixEnd_293886 5589065763975644569387 := by
  unfold tailWord_293886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1339862876663586072242689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7145935342205792385294341 1339862876663586072242689)
  ·
    refine ⟨1004897157497689554182017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1339862876663586072242689 1004897157497689554182017)
    ·
      refine ⟨753672868123267165636513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1004897157497689554182017 753672868123267165636513)
      ·
        refine ⟨565254651092450374227385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 753672868123267165636513 565254651092450374227385)
        ·
          refine ⟨423940988319337780670539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 565254651092450374227385 423940988319337780670539)
          ·
            refine ⟨635911482479006671005809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423940988319337780670539 635911482479006671005809)
            ·
              refine ⟨476933611859255003254357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635911482479006671005809 476933611859255003254357)
              ·
                refine ⟨5589065763975644569387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 476933611859255003254357 5589065763975644569387)
                ·
                  rfl

theorem cell23_293886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 8].length) (baseStart_293886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293886 prefixEnd_293886 := by exact prefixLift 293886
  have htrace : WordTrace (prefixWord ++ tailWord_293886) baseStart_293886 baseEnd_293886 := by
    simpa [prefixWord, tailWord_293886, baseEnd_293886] using wordTrace_append hprefix tailTrace_293886
  have hstable : (prefixWord ++ tailWord_293886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293886).length < 2 ^ (prefixWord ++ tailWord_293886).sum := by decide
  have hdescent : baseEnd_293886 < baseStart_293886 := by decide
  rcases family_descends (prefixWord ++ tailWord_293886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293890 : List Nat := [3, 4, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_293890 : Nat := 118140960795 + 293890 * 2 ^ 59
def prefixEnd_293890 : Nat := 4983230072969 + 3 ^ 40 * 293890 * 2
def baseEnd_293890 : Nat := 50302276516653462574477

theorem tailTrace_293890 : CollatzResearch.WordTrace tailWord_293890 prefixEnd_293890 50302276516653462574477 := by
  unfold tailWord_293890
  simp only [CollatzResearch.WordTrace]
  refine ⟨2679762226323549315271781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7146032603529464840724749 2679762226323549315271781)
  ·
    refine ⟨502455417435665496613459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2679762226323549315271781 502455417435665496613459)
    ·
      refine ⟨753683126153498244920189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 502455417435665496613459 753683126153498244920189)
      ·
        refine ⟨282631172307561841845071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 753683126153498244920189 282631172307561841845071)
        ·
          refine ⟨423946758461342762767607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282631172307561841845071 423946758461342762767607)
          ·
            refine ⟨635920137692014144151411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423946758461342762767607 635920137692014144151411)
            ·
              refine ⟨953880206538021216227117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635920137692014144151411 953880206538021216227117)
              ·
                refine ⟨357705077451757956085169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 953880206538021216227117 357705077451757956085169)
                ·
                  refine ⟨268278808088818467063877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 357705077451757956085169 268278808088818467063877)
                  ·
                    refine ⟨50302276516653462574477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 268278808088818467063877 50302276516653462574477)
                    ·
                      rfl

theorem cell23_293890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_293890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293890 prefixEnd_293890 := by exact prefixLift 293890
  have htrace : WordTrace (prefixWord ++ tailWord_293890) baseStart_293890 baseEnd_293890 := by
    simpa [prefixWord, tailWord_293890, baseEnd_293890] using wordTrace_append hprefix tailTrace_293890
  have hstable : (prefixWord ++ tailWord_293890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293890).length < 2 ^ (prefixWord ++ tailWord_293890).sum := by decide
  have hdescent : baseEnd_293890 < baseStart_293890 := by decide
  rcases family_descends (prefixWord ++ tailWord_293890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293930 : List Nat := [3, 1, 4, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_293930 : Nat := 118140960795 + 293930 * 2 ^ 59
def prefixEnd_293930 : Nat := 4983230072969 + 3 ^ 40 * 293930 * 2
def baseEnd_293930 : Nat := 150927368776140231223247

theorem tailTrace_293930 : CollatzResearch.WordTrace tailWord_293930 prefixEnd_293930 150927368776140231223247 := by
  unfold tailWord_293930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2680126956287321023135811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7147005216766189395028829 2680126956287321023135811)
  ·
    refine ⟨4020190434430981534703717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2680126956287321023135811 4020190434430981534703717)
    ·
      refine ⟨753785706455809037756947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4020190434430981534703717 753785706455809037756947)
      ·
        refine ⟨1130678559683713556635421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 753785706455809037756947 1130678559683713556635421)
        ·
          refine ⟨424004459881392583738283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1130678559683713556635421 424004459881392583738283)
          ·
            refine ⟨636006689822088875607425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424004459881392583738283 636006689822088875607425)
            ·
              refine ⟨477005017366566656705569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636006689822088875607425 477005017366566656705569)
              ·
                refine ⟨357753763024924992529177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 477005017366566656705569 357753763024924992529177)
                ·
                  refine ⟨268315322268693744396883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 357753763024924992529177 268315322268693744396883)
                  ·
                    refine ⟨402472983403040616595325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 268315322268693744396883 402472983403040616595325)
                    ·
                      refine ⟨150927368776140231223247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 402472983403040616595325 150927368776140231223247)
                      ·
                        rfl

theorem cell23_293930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_293930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293930 prefixEnd_293930 := by exact prefixLift 293930
  have htrace : WordTrace (prefixWord ++ tailWord_293930) baseStart_293930 baseEnd_293930 := by
    simpa [prefixWord, tailWord_293930, baseEnd_293930] using wordTrace_append hprefix tailTrace_293930
  have hstable : (prefixWord ++ tailWord_293930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293930).length < 2 ^ (prefixWord ++ tailWord_293930).sum := by decide
  have hdescent : baseEnd_293930 < baseStart_293930 := by decide
  rcases family_descends (prefixWord ++ tailWord_293930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293949 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_293949 : Nat := 118140960795 + 293949 * 2 ^ 59
def prefixEnd_293949 : Nat := 4983230072969 + 3 ^ 40 * 293949 * 2
def baseEnd_293949 : Nat := 150937124908575656885659

theorem tailTrace_293949 : CollatzResearch.WordTrace tailWord_293949 prefixEnd_293949 150937124908575656885659 := by
  unfold tailWord_293949
  simp only [CollatzResearch.WordTrace]
  refine ⟨10721200812080450337484901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7147467208053633558323267 10721200812080450337484901)
  ·
    refine ⟨2010225152265084438278419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10721200812080450337484901 2010225152265084438278419)
    ·
      refine ⟨3015337728397626657417629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2010225152265084438278419 3015337728397626657417629)
      ·
        refine ⟨1130751648149109996531611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3015337728397626657417629 1130751648149109996531611)
        ·
          refine ⟨1696127472223664994797417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1130751648149109996531611 1696127472223664994797417)
          ·
            refine ⟨1272095604167748746098063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1696127472223664994797417 1272095604167748746098063)
            ·
              refine ⟨1908143406251623119147095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1272095604167748746098063 1908143406251623119147095)
              ·
                refine ⟨2862215109377434678720643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1908143406251623119147095 2862215109377434678720643)
                ·
                  refine ⟨4293322664066152018080965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2862215109377434678720643 4293322664066152018080965)
                  ·
                    refine ⟨804997999512403503390181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4293322664066152018080965 804997999512403503390181)
                    ·
                      refine ⟨150937124908575656885659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 804997999512403503390181 150937124908575656885659)
                      ·
                        rfl

theorem cell23_293949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_293949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293949 prefixEnd_293949 := by exact prefixLift 293949
  have htrace : WordTrace (prefixWord ++ tailWord_293949) baseStart_293949 baseEnd_293949 := by
    simpa [prefixWord, tailWord_293949, baseEnd_293949] using wordTrace_append hprefix tailTrace_293949
  have hstable : (prefixWord ++ tailWord_293949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293949).length < 2 ^ (prefixWord ++ tailWord_293949).sum := by decide
  have hdescent : baseEnd_293949 < baseStart_293949 := by decide
  rcases family_descends (prefixWord ++ tailWord_293949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293959 : List Nat := [1, 1, 4, 1, 3, 3, 1, 2, 7]
def baseStart_293959 : Nat := 118140960795 + 293959 * 2 ^ 59
def prefixEnd_293959 : Nat := 4983230072969 + 3 ^ 40 * 293959 * 2
def baseEnd_293959 : Nat := 16771362190568957528957

theorem tailTrace_293959 : CollatzResearch.WordTrace tailWord_293959 prefixEnd_293959 16771362190568957528957 := by
  unfold tailWord_293959
  simp only [CollatzResearch.WordTrace]
  refine ⟨10721565542044222045348931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7147710361362814696899287 10721565542044222045348931)
  ·
    refine ⟨16082348313066333068023397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10721565542044222045348931 16082348313066333068023397)
    ·
      refine ⟨3015440308699937450254387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16082348313066333068023397 3015440308699937450254387)
      ·
        refine ⟨4523160463049906175381581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3015440308699937450254387 4523160463049906175381581)
        ·
          refine ⟨1696185173643714815768093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4523160463049906175381581 1696185173643714815768093)
          ·
            refine ⟨636069440116393055913035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1696185173643714815768093 636069440116393055913035)
            ·
              refine ⟨954104160174589583869553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636069440116393055913035 954104160174589583869553)
              ·
                refine ⟨715578120130942187902165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 954104160174589583869553 715578120130942187902165)
                ·
                  refine ⟨16771362190568957528957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 715578120130942187902165 16771362190568957528957)
                  ·
                    rfl

theorem cell23_293959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 7].length) (baseStart_293959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293959 prefixEnd_293959 := by exact prefixLift 293959
  have htrace : WordTrace (prefixWord ++ tailWord_293959) baseStart_293959 baseEnd_293959 := by
    simpa [prefixWord, tailWord_293959, baseEnd_293959] using wordTrace_append hprefix tailTrace_293959
  have hstable : (prefixWord ++ tailWord_293959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293959).length < 2 ^ (prefixWord ++ tailWord_293959).sum := by decide
  have hdescent : baseEnd_293959 < baseStart_293959 := by decide
  rcases family_descends (prefixWord ++ tailWord_293959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293976 : List Nat := [2, 1, 2, 2, 1, 3, 4, 3, 5]
def baseStart_293976 : Nat := 118140960795 + 293976 * 2 ^ 59
def prefixEnd_293976 : Nat := 4983230072969 + 3 ^ 40 * 293976 * 2
def baseEnd_293976 : Nat := 16772332098471894583115

theorem tailTrace_293976 : CollatzResearch.WordTrace tailWord_293976 prefixEnd_293976 16772332098471894583115 := by
  unfold tailWord_293976
  simp only [CollatzResearch.WordTrace]
  refine ⟨5361092791491316974358891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7148123721988422632478521 5361092791491316974358891)
  ·
    refine ⟨8041639187236975461538337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5361092791491316974358891 8041639187236975461538337)
    ·
      refine ⟨6031229390427731596153753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8041639187236975461538337 6031229390427731596153753)
      ·
        refine ⟨4523422042820798697115315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6031229390427731596153753 4523422042820798697115315)
        ·
          refine ⟨6785133064231198045672973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4523422042820798697115315 6785133064231198045672973)
          ·
            refine ⟨2544424899086699267127365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6785133064231198045672973 2544424899086699267127365)
            ·
              refine ⟨477079668578756112586381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2544424899086699267127365 477079668578756112586381)
              ·
                refine ⟨178904875717033542219893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 477079668578756112586381 178904875717033542219893)
                ·
                  refine ⟨16772332098471894583115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 178904875717033542219893 16772332098471894583115)
                  ·
                    rfl

theorem cell23_293976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 5].length) (baseStart_293976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293976 prefixEnd_293976 := by exact prefixLift 293976
  have htrace : WordTrace (prefixWord ++ tailWord_293976) baseStart_293976 baseEnd_293976 := by
    simpa [prefixWord, tailWord_293976, baseEnd_293976] using wordTrace_append hprefix tailTrace_293976
  have hstable : (prefixWord ++ tailWord_293976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293976).length < 2 ^ (prefixWord ++ tailWord_293976).sum := by decide
  have hdescent : baseEnd_293976 < baseStart_293976 := by decide
  rcases family_descends (prefixWord ++ tailWord_293976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293989 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 4, 5]
def baseStart_293989 : Nat := 118140960795 + 293989 * 2 ^ 59
def prefixEnd_293989 : Nat := 4983230072969 + 3 ^ 40 * 293989 * 2
def baseEnd_293989 : Nat := 50319221378251833461825

theorem tailTrace_293989 : CollatzResearch.WordTrace tailWord_293989 prefixEnd_293989 50319221378251833461825 := by
  unfold tailWord_293989
  simp only [CollatzResearch.WordTrace]
  refine ⟨10722659731935537168941021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7148439821290358112627347 10722659731935537168941021)
  ·
    refine ⟨4020997399475826438352883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10722659731935537168941021 4020997399475826438352883)
    ·
      refine ⟨6031496099213739657529325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4020997399475826438352883 6031496099213739657529325)
      ·
        refine ⟨2261811037205152371573497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6031496099213739657529325 2261811037205152371573497)
        ·
          refine ⟨1696358277903864278680123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2261811037205152371573497 1696358277903864278680123)
          ·
            refine ⟨2544537416855796418020185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1696358277903864278680123 2544537416855796418020185)
            ·
              refine ⟨1908403062641847313515139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2544537416855796418020185 1908403062641847313515139)
              ·
                refine ⟨2862604593962770970272709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1908403062641847313515139 2862604593962770970272709)
                ·
                  refine ⟨536738361368019556926133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2862604593962770970272709 536738361368019556926133)
                  ·
                    refine ⟨50319221378251833461825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 536738361368019556926133 50319221378251833461825)
                    ·
                      rfl

theorem cell23_293989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_293989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_293989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_293989 prefixEnd_293989 := by exact prefixLift 293989
  have htrace : WordTrace (prefixWord ++ tailWord_293989) baseStart_293989 baseEnd_293989 := by
    simpa [prefixWord, tailWord_293989, baseEnd_293989] using wordTrace_append hprefix tailTrace_293989
  have hstable : (prefixWord ++ tailWord_293989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293989).length < 2 ^ (prefixWord ++ tailWord_293989).sum := by decide
  have hdescent : baseEnd_293989 < baseStart_293989 := by decide
  rcases family_descends (prefixWord ++ tailWord_293989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294026 : List Nat := [3, 1, 2, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_294026 : Nat := 118140960795 + 294026 * 2 ^ 59
def prefixEnd_294026 : Nat := 4983230072969 + 3 ^ 40 * 294026 * 2
def baseEnd_294026 : Nat := 150976662918971855622805

theorem tailTrace_294026 : CollatzResearch.WordTrace tailWord_294026 prefixEnd_294026 150976662918971855622805 := by
  unfold tailWord_294026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2681002308200373122009483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7149339488534328325358621 2681002308200373122009483)
  ·
    refine ⟨4021503462300559683014225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2681002308200373122009483 4021503462300559683014225)
    ·
      refine ⟨3016127596725419762260669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4021503462300559683014225 3016127596725419762260669)
      ·
        refine ⟨1131047848772032410847751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3016127596725419762260669 1131047848772032410847751)
        ·
          refine ⟨1696571773158048616271627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1131047848772032410847751 1696571773158048616271627)
          ·
            refine ⟨2544857659737072924407441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1696571773158048616271627 2544857659737072924407441)
            ·
              refine ⟨1908643244802804693305581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2544857659737072924407441 1908643244802804693305581)
              ·
                refine ⟨715741216801051759989593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1908643244802804693305581 715741216801051759989593)
                ·
                  refine ⟨536805912600788819992195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 715741216801051759989593 536805912600788819992195)
                  ·
                    refine ⟨805208868901183229988293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 536805912600788819992195 805208868901183229988293)
                    ·
                      refine ⟨150976662918971855622805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 805208868901183229988293 150976662918971855622805)
                      ·
                        rfl

theorem cell23_294026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_294026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294026 prefixEnd_294026 := by exact prefixLift 294026
  have htrace : WordTrace (prefixWord ++ tailWord_294026) baseStart_294026 baseEnd_294026 := by
    simpa [prefixWord, tailWord_294026, baseEnd_294026] using wordTrace_append hprefix tailTrace_294026
  have hstable : (prefixWord ++ tailWord_294026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294026).length < 2 ^ (prefixWord ++ tailWord_294026).sum := by decide
  have hdescent : baseEnd_294026 < baseStart_294026 := by decide
  rcases family_descends (prefixWord ++ tailWord_294026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294049 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 8]
def baseStart_294049 : Nat := 118140960795 + 294049 * 2 ^ 59
def prefixEnd_294049 : Nat := 4983230072969 + 3 ^ 40 * 294049 * 2
def baseEnd_294049 : Nat := 16776496997113918403911

theorem tailTrace_294049 : CollatzResearch.WordTrace tailWord_294049 prefixEnd_294049 16776496997113918403911 := by
  unfold tailWord_294049
  simp only [CollatzResearch.WordTrace]
  refine ⟨10724848111718167416125201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7149898741145444944083467 10724848111718167416125201)
  ·
    refine ⟨8043636083788625562093901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10724848111718167416125201 8043636083788625562093901)
    ·
      refine ⟨3016363531420734585785213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8043636083788625562093901 3016363531420734585785213)
      ·
        refine ⟨1131136324282775469669455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3016363531420734585785213 1131136324282775469669455)
        ·
          refine ⟨1696704486424163204504183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1131136324282775469669455 1696704486424163204504183)
          ·
            refine ⟨2545056729636244806756275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1696704486424163204504183 2545056729636244806756275)
            ·
              refine ⟨3817585094454367210134413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2545056729636244806756275 3817585094454367210134413)
              ·
                refine ⟨1431594410420387703800405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3817585094454367210134413 1431594410420387703800405)
                ·
                  refine ⟨16776496997113918403911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1431594410420387703800405 16776496997113918403911)
                  ·
                    rfl

theorem cell23_294049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 8].length) (baseStart_294049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294049 prefixEnd_294049 := by exact prefixLift 294049
  have htrace : WordTrace (prefixWord ++ tailWord_294049) baseStart_294049 baseEnd_294049 := by
    simpa [prefixWord, tailWord_294049, baseEnd_294049] using wordTrace_append hprefix tailTrace_294049
  have hstable : (prefixWord ++ tailWord_294049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294049).length < 2 ^ (prefixWord ++ tailWord_294049).sum := by decide
  have hdescent : baseEnd_294049 < baseStart_294049 := by decide
  rcases family_descends (prefixWord ++ tailWord_294049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294053 : List Nat := [1, 3, 1, 2, 1, 6, 1, 1, 3, 4]
def baseStart_294053 : Nat := 118140960795 + 294053 * 2 ^ 59
def prefixEnd_294053 : Nat := 4983230072969 + 3 ^ 40 * 294053 * 2
def baseEnd_294053 : Nat := 50330175632214416661727

theorem tailTrace_294053 : CollatzResearch.WordTrace tailWord_294053 prefixEnd_294053 50330175632214416661727 := by
  unfold tailWord_294053
  simp only [CollatzResearch.WordTrace]
  refine ⟨10724994003703676099270813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7149996002469117399513875 10724994003703676099270813)
  ·
    refine ⟨4021872751388878537226555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10724994003703676099270813 4021872751388878537226555)
    ·
      refine ⟨6032809127083317805839833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4021872751388878537226555 6032809127083317805839833)
      ·
        refine ⟨4524606845312488354379875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6032809127083317805839833 4524606845312488354379875)
        ·
          refine ⟨6786910267968732531569813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4524606845312488354379875 6786910267968732531569813)
          ·
            refine ⟨318136418811034337417335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6786910267968732531569813 318136418811034337417335)
            ·
              refine ⟨477204628216551506126003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318136418811034337417335 477204628216551506126003)
              ·
                refine ⟨715806942324827259189005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 477204628216551506126003 715806942324827259189005)
                ·
                  refine ⟨268427603371810222195877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 715806942324827259189005 268427603371810222195877)
                  ·
                    refine ⟨50330175632214416661727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 268427603371810222195877 50330175632214416661727)
                    ·
                      rfl

theorem cell23_294053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_294053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294053 prefixEnd_294053 := by exact prefixLift 294053
  have htrace : WordTrace (prefixWord ++ tailWord_294053) baseStart_294053 baseEnd_294053 := by
    simpa [prefixWord, tailWord_294053, baseEnd_294053] using wordTrace_append hprefix tailTrace_294053
  have hstable : (prefixWord ++ tailWord_294053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294053).length < 2 ^ (prefixWord ++ tailWord_294053).sum := by decide
  have hdescent : baseEnd_294053 < baseStart_294053 := by decide
  rcases family_descends (prefixWord ++ tailWord_294053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294066 : List Nat := [3, 2, 1, 1, 1, 5, 1, 3, 6]
def baseStart_294066 : Nat := 118140960795 + 294066 * 2 ^ 59
def prefixEnd_294066 : Nat := 4983230072969 + 3 ^ 40 * 294066 * 2
def baseEnd_294066 : Nat := 16777466905016855458069

theorem tailTrace_294066 : CollatzResearch.WordTrace tailWord_294066 prefixEnd_294066 16777466905016855458069 := by
  unfold tailWord_294066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2681367038164144829873513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7150312101771052879662701 2681367038164144829873513)
  ·
    refine ⟨2011025278623108622405135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2681367038164144829873513 2011025278623108622405135)
    ·
      refine ⟨3016537917934662933607703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2011025278623108622405135 3016537917934662933607703)
      ·
        refine ⟨4524806876901994400411555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3016537917934662933607703 4524806876901994400411555)
        ·
          refine ⟨6787210315352991600617333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4524806876901994400411555 6787210315352991600617333)
          ·
            refine ⟨636300967064342962557875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6787210315352991600617333 636300967064342962557875)
            ·
              refine ⟨954451450596514443836813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636300967064342962557875 954451450596514443836813)
              ·
                refine ⟨357919293973692916438805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 954451450596514443836813 357919293973692916438805)
                ·
                  refine ⟨16777466905016855458069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 357919293973692916438805 16777466905016855458069)
                  ·
                    rfl

theorem cell23_294066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_294066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294066 prefixEnd_294066 := by exact prefixLift 294066
  have htrace : WordTrace (prefixWord ++ tailWord_294066) baseStart_294066 baseEnd_294066 := by
    simpa [prefixWord, tailWord_294066, baseEnd_294066] using wordTrace_append hprefix tailTrace_294066
  have hstable : (prefixWord ++ tailWord_294066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294066).length < 2 ^ (prefixWord ++ tailWord_294066).sum := by decide
  have hdescent : baseEnd_294066 < baseStart_294066 := by decide
  rcases family_descends (prefixWord ++ tailWord_294066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294100 : List Nat := [2, 4, 1, 4, 1, 1, 2, 2, 6]
def baseStart_294100 : Nat := 118140960795 + 294100 * 2 ^ 59
def prefixEnd_294100 : Nat := 4983230072969 + 3 ^ 40 * 294100 * 2
def baseEnd_294100 : Nat := 16779406720822729566385

theorem tailTrace_294100 : CollatzResearch.WordTrace tailWord_294100 prefixEnd_294100 16779406720822729566385 := by
  unfold tailWord_294100
  simp only [CollatzResearch.WordTrace]
  refine ⟨5363354117266701563115877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7151138823022268750821169 5363354117266701563115877)
  ·
    refine ⟨1005628896987506543084227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5363354117266701563115877 1005628896987506543084227)
    ·
      refine ⟨1508443345481259814626341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1005628896987506543084227 1508443345481259814626341)
      ·
        refine ⟨282833127277736215242439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1508443345481259814626341 282833127277736215242439)
        ·
          refine ⟨424249690916604322863659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282833127277736215242439 424249690916604322863659)
          ·
            refine ⟨636374536374906484295489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424249690916604322863659 636374536374906484295489)
            ·
              refine ⟨477280902281179863221617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636374536374906484295489 477280902281179863221617)
              ·
                refine ⟨357960676710884897416213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 477280902281179863221617 357960676710884897416213)
                ·
                  refine ⟨16779406720822729566385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 357960676710884897416213 16779406720822729566385)
                  ·
                    rfl

theorem cell23_294100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_294100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294100 prefixEnd_294100 := by exact prefixLift 294100
  have htrace : WordTrace (prefixWord ++ tailWord_294100) baseStart_294100 baseEnd_294100 := by
    simpa [prefixWord, tailWord_294100, baseEnd_294100] using wordTrace_append hprefix tailTrace_294100
  have hstable : (prefixWord ++ tailWord_294100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294100).length < 2 ^ (prefixWord ++ tailWord_294100).sum := by decide
  have hdescent : baseEnd_294100 < baseStart_294100 := by decide
  rcases family_descends (prefixWord ++ tailWord_294100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294103 : List Nat := [1, 1, 3, 2, 1, 2, 4, 2, 2, 3, 2]
def baseStart_294103 : Nat := 118140960795 + 294103 * 2 ^ 59
def prefixEnd_294103 : Nat := 4983230072969 + 3 ^ 40 * 294103 * 2
def baseEnd_294103 : Nat := 151016200929368054359951

theorem tailTrace_294103 : CollatzResearch.WordTrace tailWord_294103 prefixEnd_294103 151016200929368054359951 := by
  unfold tailWord_294103
  simp only [CollatzResearch.WordTrace]
  refine ⟨10726817653522534638590963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7151211769015023092393975 10726817653522534638590963)
  ·
    refine ⟨16090226480283801957886445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10726817653522534638590963 16090226480283801957886445)
    ·
      refine ⟨6033834930106425734207417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16090226480283801957886445 6033834930106425734207417)
      ·
        refine ⟨4525376197579819300655563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6033834930106425734207417 4525376197579819300655563)
        ·
          refine ⟨6788064296369728950983345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4525376197579819300655563 6788064296369728950983345)
          ·
            refine ⟨5091048222277296713237509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6788064296369728950983345 5091048222277296713237509)
            ·
              refine ⟨954571541676993133732033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5091048222277296713237509 954571541676993133732033)
              ·
                refine ⟨715928656257744850299025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 954571541676993133732033 715928656257744850299025)
                ·
                  refine ⟨536946492193308637724269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 715928656257744850299025 536946492193308637724269)
                  ·
                    refine ⟨201354934572490739146601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 536946492193308637724269 201354934572490739146601)
                    ·
                      refine ⟨151016200929368054359951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 201354934572490739146601 151016200929368054359951)
                      ·
                        rfl

theorem cell23_294103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_294103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294103 prefixEnd_294103 := by exact prefixLift 294103
  have htrace : WordTrace (prefixWord ++ tailWord_294103) baseStart_294103 baseEnd_294103 := by
    simpa [prefixWord, tailWord_294103, baseEnd_294103] using wordTrace_append hprefix tailTrace_294103
  have hstable : (prefixWord ++ tailWord_294103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294103).length < 2 ^ (prefixWord ++ tailWord_294103).sum := by decide
  have hdescent : baseEnd_294103 < baseStart_294103 := by decide
  rcases family_descends (prefixWord ++ tailWord_294103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294104 : List Nat := [2, 1, 2, 2, 6, 1, 2, 2, 1, 4]
def baseStart_294104 : Nat := 118140960795 + 294104 * 2 ^ 59
def prefixEnd_294104 : Nat := 4983230072969 + 3 ^ 40 * 294104 * 2
def baseEnd_294104 : Nat := 50338904803340850149149

theorem tailTrace_294104 : CollatzResearch.WordTrace tailWord_294104 prefixEnd_294104 50338904803340850149149 := by
  unfold tailWord_294104
  simp only [CollatzResearch.WordTrace]
  refine ⟨5363427063259455904688683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7151236084345941206251577 5363427063259455904688683)
  ·
    refine ⟨8045140594889183857033025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5363427063259455904688683 8045140594889183857033025)
    ·
      refine ⟨6033855446166887892774769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8045140594889183857033025 6033855446166887892774769)
      ·
        refine ⟨4525391584625165919581077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6033855446166887892774769 4525391584625165919581077)
        ·
          refine ⟨212127730529304652480363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4525391584625165919581077 212127730529304652480363)
          ·
            refine ⟨318191595793956978720545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212127730529304652480363 318191595793956978720545)
            ·
              refine ⟨238643696845467734040409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318191595793956978720545 238643696845467734040409)
              ·
                refine ⟨178982772634100800530307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238643696845467734040409 178982772634100800530307)
                ·
                  refine ⟨268474158951151200795461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178982772634100800530307 268474158951151200795461)
                  ·
                    refine ⟨50338904803340850149149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 268474158951151200795461 50338904803340850149149)
                    ·
                      rfl

theorem cell23_294104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 1, 4].length) (baseStart_294104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294104 prefixEnd_294104 := by exact prefixLift 294104
  have htrace : WordTrace (prefixWord ++ tailWord_294104) baseStart_294104 baseEnd_294104 := by
    simpa [prefixWord, tailWord_294104, baseEnd_294104] using wordTrace_append hprefix tailTrace_294104
  have hstable : (prefixWord ++ tailWord_294104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294104).length < 2 ^ (prefixWord ++ tailWord_294104).sum := by decide
  have hdescent : baseEnd_294104 < baseStart_294104 := by decide
  rcases family_descends (prefixWord ++ tailWord_294104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294116 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_294116 : Nat := 118140960795 + 294116 * 2 ^ 59
def prefixEnd_294116 : Nat := 4983230072969 + 3 ^ 40 * 294116 * 2
def baseEnd_294116 : Nat := 151022876177876503497391

theorem tailTrace_294116 : CollatzResearch.WordTrace tailWord_294116 prefixEnd_294116 151022876177876503497391 := by
  unfold tailWord_294116
  simp only [CollatzResearch.WordTrace]
  refine ⟨5363645901237718929407101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7151527868316958572542801 5363645901237718929407101)
  ·
    refine ⟨2011367212964144598527663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5363645901237718929407101 2011367212964144598527663)
    ·
      refine ⟨3017050819446216897791495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2011367212964144598527663 3017050819446216897791495)
      ·
        refine ⟨4525576229169325346687243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3017050819446216897791495 4525576229169325346687243)
        ·
          refine ⟨6788364343753988020030865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4525576229169325346687243 6788364343753988020030865)
          ·
            refine ⟨5091273257815491015023149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6788364343753988020030865 5091273257815491015023149)
            ·
              refine ⟨1909227471680809130633681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5091273257815491015023149 1909227471680809130633681)
              ·
                refine ⟨1431920603760606847975261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1909227471680809130633681 1431920603760606847975261)
                ·
                  refine ⟨536970226410227567990723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1431920603760606847975261 536970226410227567990723)
                  ·
                    refine ⟨805455339615341351986085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 536970226410227567990723 805455339615341351986085)
                    ·
                      refine ⟨151022876177876503497391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 805455339615341351986085 151022876177876503497391)
                      ·
                        rfl

theorem cell23_294116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_294116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294116 prefixEnd_294116 := by exact prefixLift 294116
  have htrace : WordTrace (prefixWord ++ tailWord_294116) baseStart_294116 baseEnd_294116 := by
    simpa [prefixWord, tailWord_294116, baseEnd_294116] using wordTrace_append hprefix tailTrace_294116
  have hstable : (prefixWord ++ tailWord_294116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294116).length < 2 ^ (prefixWord ++ tailWord_294116).sum := by decide
  have hdescent : baseEnd_294116 < baseStart_294116 := by decide
  rcases family_descends (prefixWord ++ tailWord_294116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294126 : List Nat := [4, 1, 2, 1, 1, 1, 3, 3, 1, 6]
def baseStart_294126 : Nat := 118140960795 + 294126 * 2 ^ 59
def prefixEnd_294126 : Nat := 4983230072969 + 3 ^ 40 * 294126 * 2
def baseEnd_294126 : Nat := 50342670328140488124115

theorem tailTrace_294126 : CollatzResearch.WordTrace tailWord_294126 prefixEnd_294126 50342670328140488124115 := by
  unfold tailWord_294126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1340957066554901195834779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7151771021626139711118821 1340957066554901195834779)
  ·
    refine ⟨2011435599832351793752169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1340957066554901195834779 2011435599832351793752169)
    ·
      refine ⟨1508576699874263845314127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2011435599832351793752169 1508576699874263845314127)
      ·
        refine ⟨2262865049811395767971191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1508576699874263845314127 2262865049811395767971191)
        ·
          refine ⟨3394297574717093651956787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2262865049811395767971191 3394297574717093651956787)
          ·
            refine ⟨5091446362075640477935181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3394297574717093651956787 5091446362075640477935181)
            ·
              refine ⟨1909292385778365179225693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5091446362075640477935181 1909292385778365179225693)
              ·
                refine ⟨715984644666886942209635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1909292385778365179225693 715984644666886942209635)
                ·
                  refine ⟨1073976967000330413314453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 715984644666886942209635 1073976967000330413314453)
                  ·
                    refine ⟨50342670328140488124115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1073976967000330413314453 50342670328140488124115)
                    ·
                      rfl

theorem cell23_294126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_294126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294126 prefixEnd_294126 := by exact prefixLift 294126
  have htrace : WordTrace (prefixWord ++ tailWord_294126) baseStart_294126 baseEnd_294126 := by
    simpa [prefixWord, tailWord_294126, baseEnd_294126] using wordTrace_append hprefix tailTrace_294126
  have hstable : (prefixWord ++ tailWord_294126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294126).length < 2 ^ (prefixWord ++ tailWord_294126).sum := by decide
  have hdescent : baseEnd_294126 < baseStart_294126 := by decide
  rcases family_descends (prefixWord ++ tailWord_294126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294153 : List Nat := [1, 2, 1, 1, 3, 3, 3, 3, 1, 2, 3]
def baseStart_294153 : Nat := 118140960795 + 294153 * 2 ^ 59
def prefixEnd_294153 : Nat := 4983230072969 + 3 ^ 40 * 294153 * 2
def baseEnd_294153 : Nat := 151041874962092858734721

theorem tailTrace_294153 : CollatzResearch.WordTrace tailWord_294153 prefixEnd_294153 151041874962092858734721 := by
  unfold tailWord_294153
  simp only [CollatzResearch.WordTrace]
  refine ⟨10728641303341393177911113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7152427535560928785274075 10728641303341393177911113)
  ·
    refine ⟨8046480977506044883433335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10728641303341393177911113 8046480977506044883433335)
    ·
      refine ⟨12069721466259067325150003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8046480977506044883433335 12069721466259067325150003)
      ·
        refine ⟨18104582199388600987725005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12069721466259067325150003 18104582199388600987725005)
        ·
          refine ⟨6789218324770725370396877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18104582199388600987725005 6789218324770725370396877)
          ·
            refine ⟨2545956871789022013898829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6789218324770725370396877 2545956871789022013898829)
            ·
              refine ⟨954733826920883255212061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2545956871789022013898829 954733826920883255212061)
              ·
                refine ⟨358025185095331220704523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 954733826920883255212061 358025185095331220704523)
                ·
                  refine ⟨537037777642996831056785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 358025185095331220704523 537037777642996831056785)
                  ·
                    refine ⟨402778333232247623292589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 537037777642996831056785 402778333232247623292589)
                    ·
                      refine ⟨151041874962092858734721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 402778333232247623292589 151041874962092858734721)
                      ·
                        rfl

theorem cell23_294153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 2, 3].length) (baseStart_294153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294153 prefixEnd_294153 := by exact prefixLift 294153
  have htrace : WordTrace (prefixWord ++ tailWord_294153) baseStart_294153 baseEnd_294153 := by
    simpa [prefixWord, tailWord_294153, baseEnd_294153] using wordTrace_append hprefix tailTrace_294153
  have hstable : (prefixWord ++ tailWord_294153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294153).length < 2 ^ (prefixWord ++ tailWord_294153).sum := by decide
  have hdescent : baseEnd_294153 < baseStart_294153 := by decide
  rcases family_descends (prefixWord ++ tailWord_294153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294159 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 6]
def baseStart_294159 : Nat := 118140960795 + 294159 * 2 ^ 59
def prefixEnd_294159 : Nat := 4983230072969 + 3 ^ 40 * 294159 * 2
def baseEnd_294159 : Nat := 151044955846019835259693

theorem tailTrace_294159 : CollatzResearch.WordTrace tailWord_294159 prefixEnd_294159 151044955846019835259693 := by
  unfold tailWord_294159
  simp only [CollatzResearch.WordTrace]
  refine ⟨10728860141319656202629531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7152573427546437468419687 10728860141319656202629531)
  ·
    refine ⟨16093290211979484303944297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10728860141319656202629531 16093290211979484303944297)
    ·
      refine ⟨12069967658984613227958223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16093290211979484303944297 12069967658984613227958223)
      ·
        refine ⟨18104951488476919841937335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12069967658984613227958223 18104951488476919841937335)
        ·
          refine ⟨27157427232715379762906003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18104951488476919841937335 27157427232715379762906003)
          ·
            refine ⟨40736140849073069644359005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27157427232715379762906003 40736140849073069644359005)
            ·
              refine ⟨15276052818402401116634627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40736140849073069644359005 15276052818402401116634627)
              ·
                refine ⟨22914079227603601674951941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15276052818402401116634627 22914079227603601674951941)
                ·
                  refine ⟨4296389855175675314053489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22914079227603601674951941 4296389855175675314053489)
                  ·
                    refine ⟨3222292391381756485540117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4296389855175675314053489 3222292391381756485540117)
                    ·
                      refine ⟨151044955846019835259693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3222292391381756485540117 151044955846019835259693)
                      ·
                        rfl

theorem cell23_294159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_294159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294159 prefixEnd_294159 := by exact prefixLift 294159
  have htrace : WordTrace (prefixWord ++ tailWord_294159) baseStart_294159 baseEnd_294159 := by
    simpa [prefixWord, tailWord_294159, baseEnd_294159] using wordTrace_append hprefix tailTrace_294159
  have hstable : (prefixWord ++ tailWord_294159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294159).length < 2 ^ (prefixWord ++ tailWord_294159).sum := by decide
  have hdescent : baseEnd_294159 < baseStart_294159 := by decide
  rcases family_descends (prefixWord ++ tailWord_294159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294167 : List Nat := [1, 1, 3, 4, 1, 1, 1, 6, 1, 2, 2]
def baseStart_294167 : Nat := 118140960795 + 294167 * 2 ^ 59
def prefixEnd_294167 : Nat := 4983230072969 + 3 ^ 40 * 294167 * 2
def baseEnd_294167 : Nat := 151049063691255803959657

theorem tailTrace_294167 : CollatzResearch.WordTrace tailWord_294167 prefixEnd_294167 151049063691255803959657 := by
  unfold tailWord_294167
  simp only [CollatzResearch.WordTrace]
  refine ⟨10729151925290673568920755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7152767950193782379280503 10729151925290673568920755)
  ·
    refine ⟨16093727887936010353381133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10729151925290673568920755 16093727887936010353381133)
    ·
      refine ⟨6035147957976003882517925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16093727887936010353381133 6035147957976003882517925)
      ·
        refine ⟨1131590242120500727972111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6035147957976003882517925 1131590242120500727972111)
        ·
          refine ⟨1697385363180751091958167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1131590242120500727972111 1697385363180751091958167)
          ·
            refine ⟨2546078044771126637937251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1697385363180751091958167 2546078044771126637937251)
            ·
              refine ⟨3819117067156689956905877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2546078044771126637937251 3819117067156689956905877)
              ·
                refine ⟨179021112522969841729963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3819117067156689956905877 179021112522969841729963)
                ·
                  refine ⟨268531668784454762594945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179021112522969841729963 268531668784454762594945)
                  ·
                    refine ⟨201398751588341071946209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 268531668784454762594945 201398751588341071946209)
                    ·
                      refine ⟨151049063691255803959657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 201398751588341071946209 151049063691255803959657)
                      ·
                        rfl

theorem cell23_294167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_294167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294167 prefixEnd_294167 := by exact prefixLift 294167
  have htrace : WordTrace (prefixWord ++ tailWord_294167) baseStart_294167 baseEnd_294167 := by
    simpa [prefixWord, tailWord_294167, baseEnd_294167] using wordTrace_append hprefix tailTrace_294167
  have hstable : (prefixWord ++ tailWord_294167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294167).length < 2 ^ (prefixWord ++ tailWord_294167).sum := by decide
  have hdescent : baseEnd_294167 < baseStart_294167 := by decide
  rcases family_descends (prefixWord ++ tailWord_294167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294201 : List Nat := [1, 2, 1, 6, 2, 2, 1, 3, 1, 2, 2]
def baseStart_294201 : Nat := 118140960795 + 294201 * 2 ^ 59
def prefixEnd_294201 : Nat := 4983230072969 + 3 ^ 40 * 294201 * 2
def baseEnd_294201 : Nat := 151066522033508670934501

theorem tailTrace_294201 : CollatzResearch.WordTrace tailWord_294201 prefixEnd_294201 151066522033508670934501 := by
  unfold tailWord_294201
  simp only [CollatzResearch.WordTrace]
  refine ⟨10730392007167497375658457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7153594671444998250438971 10730392007167497375658457)
  ·
    refine ⟨8047794005375623031743843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10730392007167497375658457 8047794005375623031743843)
    ·
      refine ⟨12071691008063434547615765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8047794005375623031743843 12071691008063434547615765)
      ·
        refine ⟨565860516002973494419489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12071691008063434547615765 565860516002973494419489)
        ·
          refine ⟨424395387002230120814617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 565860516002973494419489 424395387002230120814617)
          ·
            refine ⟨318296540251672590610963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 424395387002230120814617 318296540251672590610963)
            ·
              refine ⟨477444810377508885916445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318296540251672590610963 477444810377508885916445)
              ·
                refine ⟨179041803891565832218667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 477444810377508885916445 179041803891565832218667)
                ·
                  refine ⟨268562705837348748328001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179041803891565832218667 268562705837348748328001)
                  ·
                    refine ⟨201422029378011561246001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 268562705837348748328001 201422029378011561246001)
                    ·
                      refine ⟨151066522033508670934501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 201422029378011561246001 151066522033508670934501)
                      ·
                        rfl

theorem cell23_294201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_294201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294201 prefixEnd_294201 := by exact prefixLift 294201
  have htrace : WordTrace (prefixWord ++ tailWord_294201) baseStart_294201 baseEnd_294201 := by
    simpa [prefixWord, tailWord_294201, baseEnd_294201] using wordTrace_append hprefix tailTrace_294201
  have hstable : (prefixWord ++ tailWord_294201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294201).length < 2 ^ (prefixWord ++ tailWord_294201).sum := by decide
  have hdescent : baseEnd_294201 < baseStart_294201 := by decide
  rcases family_descends (prefixWord ++ tailWord_294201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294226 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_294226 : Nat := 118140960795 + 294226 * 2 ^ 59
def prefixEnd_294226 : Nat := 4983230072969 + 3 ^ 40 * 294226 * 2
def baseEnd_294226 : Nat := 151079359049871073121885

theorem tailTrace_294226 : CollatzResearch.WordTrace tailWord_294226 prefixEnd_294226 151079359049871073121885 := by
  unfold tailWord_294226
  simp only [CollatzResearch.WordTrace]
  refine ⟨2682825958019231661329633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7154202554717951096879021 2682825958019231661329633)
  ·
    refine ⟨2012119468514423745997225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2682825958019231661329633 2012119468514423745997225)
    ·
      refine ⟨1509089601385817809497919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2012119468514423745997225 1509089601385817809497919)
      ·
        refine ⟨2263634402078726714246879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1509089601385817809497919 2263634402078726714246879)
        ·
          refine ⟨3395451603118090071370319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2263634402078726714246879 3395451603118090071370319)
          ·
            refine ⟨5093177404677135107055479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3395451603118090071370319 5093177404677135107055479)
            ·
              refine ⟨7639766107015702660583219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5093177404677135107055479 7639766107015702660583219)
              ·
                refine ⟨11459649160523553990874829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7639766107015702660583219 11459649160523553990874829)
                ·
                  refine ⟨4297368435196332746578061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11459649160523553990874829 4297368435196332746578061)
                  ·
                    refine ⟨1611513163198624779966773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4297368435196332746578061 1611513163198624779966773)
                    ·
                      refine ⟨151079359049871073121885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1611513163198624779966773 151079359049871073121885)
                      ·
                        rfl

theorem cell23_294226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_294226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294226 prefixEnd_294226 := by exact prefixLift 294226
  have htrace : WordTrace (prefixWord ++ tailWord_294226) baseStart_294226 baseEnd_294226 := by
    simpa [prefixWord, tailWord_294226, baseEnd_294226] using wordTrace_append hprefix tailTrace_294226
  have hstable : (prefixWord ++ tailWord_294226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294226).length < 2 ^ (prefixWord ++ tailWord_294226).sum := by decide
  have hdescent : baseEnd_294226 < baseStart_294226 := by decide
  rcases family_descends (prefixWord ++ tailWord_294226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294263 : List Nat := [1, 1, 3, 1, 1, 2, 4, 5, 5]
def baseStart_294263 : Nat := 118140960795 + 294263 * 2 ^ 59
def prefixEnd_294263 : Nat := 4983230072969 + 3 ^ 40 * 294263 * 2
def baseEnd_294263 : Nat := 16788706426009714262135

theorem tailTrace_294263 : CollatzResearch.WordTrace tailWord_294263 prefixEnd_294263 16788706426009714262135 := by
  unfold tailWord_294263
  simp only [CollatzResearch.WordTrace]
  refine ⟨10732653332942881964415443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7155102221961921309610295 10732653332942881964415443)
  ·
    refine ⟨16098979999414322946623165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10732653332942881964415443 16098979999414322946623165)
    ·
      refine ⟨6037117499780371104983687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16098979999414322946623165 6037117499780371104983687)
      ·
        refine ⟨9055676249670556657475531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6037117499780371104983687 9055676249670556657475531)
        ·
          refine ⟨13583514374505834986213297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9055676249670556657475531 13583514374505834986213297)
          ·
            refine ⟨10187635780879376239659973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13583514374505834986213297 10187635780879376239659973)
            ·
              refine ⟨1910181708914883044936245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10187635780879376239659973 1910181708914883044936245)
              ·
                refine ⟨179079535210770285462773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1910181708914883044936245 179079535210770285462773)
                ·
                  refine ⟨16788706426009714262135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 179079535210770285462773 16788706426009714262135)
                  ·
                    rfl

theorem cell23_294263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 5].length) (baseStart_294263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294263 prefixEnd_294263 := by exact prefixLift 294263
  have htrace : WordTrace (prefixWord ++ tailWord_294263) baseStart_294263 baseEnd_294263 := by
    simpa [prefixWord, tailWord_294263, baseEnd_294263] using wordTrace_append hprefix tailTrace_294263
  have hstable : (prefixWord ++ tailWord_294263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294263).length < 2 ^ (prefixWord ++ tailWord_294263).sum := by decide
  have hdescent : baseEnd_294263 < baseStart_294263 := by decide
  rcases family_descends (prefixWord ++ tailWord_294263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294280 : List Nat := [2, 1, 3, 3, 1, 3, 1, 4, 5]
def baseStart_294280 : Nat := 118140960795 + 294280 * 2 ^ 59
def prefixEnd_294280 : Nat := 4983230072969 + 3 ^ 40 * 294280 * 2
def baseEnd_294280 : Nat := 16789676333912651316293

theorem tailTrace_294280 : CollatzResearch.WordTrace tailWord_294280 prefixEnd_294280 16789676333912651316293 := by
  unfold tailWord_294280
  simp only [CollatzResearch.WordTrace]
  refine ⟨5366636686940646933892147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7155515582587529245189529 5366636686940646933892147)
  ·
    refine ⟨8049955030410970400838221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5366636686940646933892147 8049955030410970400838221)
    ·
      refine ⟨3018733136404113900314333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8049955030410970400838221 3018733136404113900314333)
      ·
        refine ⟨1132024926151542712617875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3018733136404113900314333 1132024926151542712617875)
        ·
          refine ⟨1698037389227314068926813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132024926151542712617875 1698037389227314068926813)
          ·
            refine ⟨636764020960242775847555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1698037389227314068926813 636764020960242775847555)
            ·
              refine ⟨955146031440364163771333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636764020960242775847555 955146031440364163771333)
              ·
                refine ⟨179089880895068280707125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 955146031440364163771333 179089880895068280707125)
                ·
                  refine ⟨16789676333912651316293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 179089880895068280707125 16789676333912651316293)
                  ·
                    rfl

theorem cell23_294280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 5].length) (baseStart_294280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294280 prefixEnd_294280 := by exact prefixLift 294280
  have htrace : WordTrace (prefixWord ++ tailWord_294280) baseStart_294280 baseEnd_294280 := by
    simpa [prefixWord, tailWord_294280, baseEnd_294280] using wordTrace_append hprefix tailTrace_294280
  have hstable : (prefixWord ++ tailWord_294280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294280).length < 2 ^ (prefixWord ++ tailWord_294280).sum := by decide
  have hdescent : baseEnd_294280 < baseStart_294280 := by decide
  rcases family_descends (prefixWord ++ tailWord_294280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294283 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 1, 7, 2]
def baseStart_294283 : Nat := 118140960795 + 294283 * 2 ^ 59
def prefixEnd_294283 : Nat := 4983230072969 + 3 ^ 40 * 294283 * 2
def baseEnd_294283 : Nat := 151108627447177350109123

theorem tailTrace_294283 : CollatzResearch.WordTrace tailWord_294283 prefixEnd_294283 151108627447177350109123 := by
  unfold tailWord_294283
  simp only [CollatzResearch.WordTrace]
  refine ⟨10733382792870425380143503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7155588528580283586762335 10733382792870425380143503)
  ·
    refine ⟨16100074189305638070215255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10733382792870425380143503 16100074189305638070215255)
    ·
      refine ⟨24150111283958457105322883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16100074189305638070215255 24150111283958457105322883)
      ·
        refine ⟨36225166925937685657984325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24150111283958457105322883 36225166925937685657984325)
        ·
          refine ⟨6792218798613316060872061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36225166925937685657984325 6792218798613316060872061)
          ·
            refine ⟨2547082049479993522827023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6792218798613316060872061 2547082049479993522827023)
            ·
              refine ⟨3820623074219990284240535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2547082049479993522827023 3820623074219990284240535)
              ·
                refine ⟨5730934611329985426360803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3820623074219990284240535 5730934611329985426360803)
                ·
                  refine ⟨8596401916994978139541205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5730934611329985426360803 8596401916994978139541205)
                  ·
                    refine ⟨201478169929569800145497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8596401916994978139541205 201478169929569800145497)
                    ·
                      refine ⟨151108627447177350109123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 201478169929569800145497 151108627447177350109123)
                      ·
                        rfl

theorem cell23_294283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 7, 2].length) (baseStart_294283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294283 prefixEnd_294283 := by exact prefixLift 294283
  have htrace : WordTrace (prefixWord ++ tailWord_294283) baseStart_294283 baseEnd_294283 := by
    simpa [prefixWord, tailWord_294283, baseEnd_294283] using wordTrace_append hprefix tailTrace_294283
  have hstable : (prefixWord ++ tailWord_294283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294283).length < 2 ^ (prefixWord ++ tailWord_294283).sum := by decide
  have hdescent : baseEnd_294283 < baseStart_294283 := by decide
  rcases family_descends (prefixWord ++ tailWord_294283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294397 : List Nat := [1, 4, 1, 1, 1, 4, 3, 1, 3, 1, 3]
def baseStart_294397 : Nat := 118140960795 + 294397 * 2 ^ 59
def prefixEnd_294397 : Nat := 4983230072969 + 3 ^ 40 * 294397 * 2
def baseEnd_294397 : Nat := 151167164241789904083599

theorem tailTrace_294397 : CollatzResearch.WordTrace tailWord_294397 prefixEnd_294397 151167164241789904083599 := by
  unfold tailWord_294397
  simp only [CollatzResearch.WordTrace]
  refine ⟨10737540714457422849793445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7158360476304948566528963 10737540714457422849793445)
  ·
    refine ⟨2013288883960766784336271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10737540714457422849793445 2013288883960766784336271)
    ·
      refine ⟨3019933325941150176504407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2013288883960766784336271 3019933325941150176504407)
      ·
        refine ⟨4529899988911725264756611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3019933325941150176504407 4529899988911725264756611)
        ·
          refine ⟨6794849983367587897134917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4529899988911725264756611 6794849983367587897134917)
          ·
            refine ⟨1274034371881422730712797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6794849983367587897134917 1274034371881422730712797)
            ·
              refine ⟨477762889455533524017299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1274034371881422730712797 477762889455533524017299)
              ·
                refine ⟨716644334183300286025949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 477762889455533524017299 716644334183300286025949)
                ·
                  refine ⟨268741625318737607259731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 716644334183300286025949 268741625318737607259731)
                  ·
                    refine ⟨403112437978106410889597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 268741625318737607259731 403112437978106410889597)
                    ·
                      refine ⟨151167164241789904083599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 403112437978106410889597 151167164241789904083599)
                      ·
                        rfl

theorem cell23_294397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_294397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294397 prefixEnd_294397 := by exact prefixLift 294397
  have htrace : WordTrace (prefixWord ++ tailWord_294397) baseStart_294397 baseEnd_294397 := by
    simpa [prefixWord, tailWord_294397, baseEnd_294397] using wordTrace_append hprefix tailTrace_294397
  have hstable : (prefixWord ++ tailWord_294397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294397).length < 2 ^ (prefixWord ++ tailWord_294397).sum := by decide
  have hdescent : baseEnd_294397 < baseStart_294397 := by decide
  rcases family_descends (prefixWord ++ tailWord_294397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294404 : List Nat := [2, 3, 2, 3, 2, 2, 2, 1, 6]
def baseStart_294404 : Nat := 118140960795 + 294404 * 2 ^ 59
def prefixEnd_294404 : Nat := 4983230072969 + 3 ^ 40 * 294404 * 2
def baseEnd_294404 : Nat := 16796750956263486299563

theorem tailTrace_294404 : CollatzResearch.WordTrace tailWord_294404 prefixEnd_294404 16796750956263486299563 := by
  unfold tailWord_294404
  simp only [CollatzResearch.WordTrace]
  refine ⟨5368898012716031522649133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7158530683621375363532177 5368898012716031522649133)
  ·
    refine ⟨2013336754768511820993425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5368898012716031522649133 2013336754768511820993425)
    ·
      refine ⟨1510002566076383865745069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2013336754768511820993425 1510002566076383865745069)
      ·
        refine ⟨566250962278643949654401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1510002566076383865745069 566250962278643949654401)
        ·
          refine ⟨424688221708982962240801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 566250962278643949654401 424688221708982962240801)
          ·
            refine ⟨318516166281737221680601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 424688221708982962240801 318516166281737221680601)
            ·
              refine ⟨238887124711302916260451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318516166281737221680601 238887124711302916260451)
              ·
                refine ⟨358330687066954374390677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238887124711302916260451 358330687066954374390677)
                ·
                  refine ⟨16796750956263486299563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 358330687066954374390677 16796750956263486299563)
                  ·
                    rfl

theorem cell23_294404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_294404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294404 prefixEnd_294404 := by exact prefixLift 294404
  have htrace : WordTrace (prefixWord ++ tailWord_294404) baseStart_294404 baseEnd_294404 := by
    simpa [prefixWord, tailWord_294404, baseEnd_294404] using wordTrace_append hprefix tailTrace_294404
  have hstable : (prefixWord ++ tailWord_294404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294404).length < 2 ^ (prefixWord ++ tailWord_294404).sum := by decide
  have hdescent : baseEnd_294404 < baseStart_294404 := by decide
  rcases family_descends (prefixWord ++ tailWord_294404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294424 : List Nat := [2, 1, 2, 3, 4, 1, 2, 1, 2, 3, 2]
def baseStart_294424 : Nat := 118140960795 + 294424 * 2 ^ 59
def prefixEnd_294424 : Nat := 4983230072969 + 3 ^ 40 * 294424 * 2
def baseEnd_294424 : Nat := 151181028219461298445975

theorem tailTrace_294424 : CollatzResearch.WordTrace tailWord_294424 prefixEnd_294424 151181028219461298445975 := by
  unfold tailWord_294424
  simp only [CollatzResearch.WordTrace]
  refine ⟨5369262742679803230513163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7159016990239737640684217 5369262742679803230513163)
  ·
    refine ⟨8053894114019704845769745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5369262742679803230513163 8053894114019704845769745)
    ·
      refine ⟨6040420585514778634327309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8053894114019704845769745 6040420585514778634327309)
      ·
        refine ⟨2265157719568041987872741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6040420585514778634327309 2265157719568041987872741)
        ·
          refine ⟨424717072419007872726139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2265157719568041987872741 424717072419007872726139)
          ·
            refine ⟨637075608628511809089209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424717072419007872726139 637075608628511809089209)
            ·
              refine ⟨477806706471383856816907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 637075608628511809089209 477806706471383856816907)
              ·
                refine ⟨716710059707075785225361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 477806706471383856816907 716710059707075785225361)
                ·
                  refine ⟨537532544780306838919021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 716710059707075785225361 537532544780306838919021)
                  ·
                    refine ⟨201574704292615064594633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 537532544780306838919021 201574704292615064594633)
                    ·
                      refine ⟨151181028219461298445975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 201574704292615064594633 151181028219461298445975)
                      ·
                        rfl

theorem cell23_294424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_294424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294424 prefixEnd_294424 := by exact prefixLift 294424
  have htrace : WordTrace (prefixWord ++ tailWord_294424) baseStart_294424 baseEnd_294424 := by
    simpa [prefixWord, tailWord_294424, baseEnd_294424] using wordTrace_append hprefix tailTrace_294424
  have hstable : (prefixWord ++ tailWord_294424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294424).length < 2 ^ (prefixWord ++ tailWord_294424).sum := by decide
  have hdescent : baseEnd_294424 < baseStart_294424 := by decide
  rcases family_descends (prefixWord ++ tailWord_294424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294504 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_294504 : Nat := 118140960795 + 294504 * 2 ^ 59
def prefixEnd_294504 : Nat := 4983230072969 + 3 ^ 40 * 294504 * 2
def baseEnd_294504 : Nat := 151222106671820985445607

theorem tailTrace_294504 : CollatzResearch.WordTrace tailWord_294504 prefixEnd_294504 151222106671820985445607 := by
  unfold tailWord_294504
  simp only [CollatzResearch.WordTrace]
  refine ⟨5370721662534890061969283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7160962216713186749292377 5370721662534890061969283)
  ·
    refine ⟨8056082493802335092953925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5370721662534890061969283 8056082493802335092953925)
    ·
      refine ⟨1510515467587937829928861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8056082493802335092953925 1510515467587937829928861)
      ·
        refine ⟨566443300345476686223323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1510515467587937829928861 566443300345476686223323)
        ·
          refine ⟨849664950518215029334985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566443300345476686223323 849664950518215029334985)
          ·
            refine ⟨637248712888661272001239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 849664950518215029334985 637248712888661272001239)
            ·
              refine ⟨955873069332991908001859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637248712888661272001239 955873069332991908001859)
              ·
                refine ⟨1433809603999487862002789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 955873069332991908001859 1433809603999487862002789)
                ·
                  refine ⟨268839300749903974125523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1433809603999487862002789 268839300749903974125523)
                  ·
                    refine ⟨403258951124855961188285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 268839300749903974125523 403258951124855961188285)
                    ·
                      refine ⟨151222106671820985445607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 403258951124855961188285 151222106671820985445607)
                      ·
                        rfl

theorem cell23_294504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_294504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294504 prefixEnd_294504 := by exact prefixLift 294504
  have htrace : WordTrace (prefixWord ++ tailWord_294504) baseStart_294504 baseEnd_294504 := by
    simpa [prefixWord, tailWord_294504, baseEnd_294504] using wordTrace_append hprefix tailTrace_294504
  have hstable : (prefixWord ++ tailWord_294504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294504).length < 2 ^ (prefixWord ++ tailWord_294504).sum := by decide
  have hdescent : baseEnd_294504 < baseStart_294504 := by decide
  rcases family_descends (prefixWord ++ tailWord_294504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294543 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 7]
def baseStart_294543 : Nat := 118140960795 + 294543 * 2 ^ 59
def prefixEnd_294543 : Nat := 4983230072969 + 3 ^ 40 * 294543 * 2
def baseEnd_294543 : Nat := 151242132417346332857927

theorem tailTrace_294543 : CollatzResearch.WordTrace tailWord_294543 prefixEnd_294543 151242132417346332857927 := by
  unfold tailWord_294543
  simp only [CollatzResearch.WordTrace]
  refine ⟨10742865771928489784608283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7161910514618993189738855 10742865771928489784608283)
  ·
    refine ⟨16114298657892734676912425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10742865771928489784608283 16114298657892734676912425)
    ·
      refine ⟨12085723993419551007684319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16114298657892734676912425 12085723993419551007684319)
      ·
        refine ⟨18128585990129326511526479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12085723993419551007684319 18128585990129326511526479)
        ·
          refine ⟨27192878985193989767289719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18128585990129326511526479 27192878985193989767289719)
          ·
            refine ⟨40789318477790984650934579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27192878985193989767289719 40789318477790984650934579)
            ·
              refine ⟨61183977716686476976401869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40789318477790984650934579 61183977716686476976401869)
              ·
                refine ⟨22943991643757428866150701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61183977716686476976401869 22943991643757428866150701)
                ·
                  refine ⟨8603996866409035824806513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22943991643757428866150701 8603996866409035824806513)
                  ·
                    refine ⟨6452997649806776868604885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8603996866409035824806513 6452997649806776868604885)
                    ·
                      refine ⟨151242132417346332857927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6452997649806776868604885 151242132417346332857927)
                      ·
                        rfl

theorem cell23_294543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_294543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294543 prefixEnd_294543 := by exact prefixLift 294543
  have htrace : WordTrace (prefixWord ++ tailWord_294543) baseStart_294543 baseEnd_294543 := by
    simpa [prefixWord, tailWord_294543, baseEnd_294543] using wordTrace_append hprefix tailTrace_294543
  have hstable : (prefixWord ++ tailWord_294543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294543).length < 2 ^ (prefixWord ++ tailWord_294543).sum := by decide
  have hdescent : baseEnd_294543 < baseStart_294543 := by decide
  rcases family_descends (prefixWord ++ tailWord_294543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294617 : List Nat := [1, 2, 1, 2, 3, 3, 2, 2, 2, 1, 4]
def baseStart_294617 : Nat := 118140960795 + 294617 * 2 ^ 59
def prefixEnd_294617 : Nat := 4983230072969 + 3 ^ 40 * 294617 * 2
def baseEnd_294617 : Nat := 151280129985779043332587

theorem tailTrace_294617 : CollatzResearch.WordTrace tailWord_294617 prefixEnd_294617 151280129985779043332587 := by
  unfold tailWord_294617
  simp only [CollatzResearch.WordTrace]
  refine ⟨10745564773660400422802105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7163709849106933615201403 10745564773660400422802105)
  ·
    refine ⟨8059173580245300317101579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10745564773660400422802105 8059173580245300317101579)
    ·
      refine ⟨12088760370367950475652369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8059173580245300317101579 12088760370367950475652369)
      ·
        refine ⟨9066570277775962856739277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12088760370367950475652369 9066570277775962856739277)
        ·
          refine ⟨3399963854165986071277229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9066570277775962856739277 3399963854165986071277229)
          ·
            refine ⟨1274986445312244776728961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3399963854165986071277229 1274986445312244776728961)
            ·
              refine ⟨956239833984183582546721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1274986445312244776728961 956239833984183582546721)
              ·
                refine ⟨717179875488137686910041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 956239833984183582546721 717179875488137686910041)
                ·
                  refine ⟨537884906616103265182531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 717179875488137686910041 537884906616103265182531)
                  ·
                    refine ⟨806827359924154897773797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 537884906616103265182531 806827359924154897773797)
                    ·
                      refine ⟨151280129985779043332587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 806827359924154897773797 151280129985779043332587)
                      ·
                        rfl

theorem cell23_294617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_294617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294617 prefixEnd_294617 := by exact prefixLift 294617
  have htrace : WordTrace (prefixWord ++ tailWord_294617) baseStart_294617 baseEnd_294617 := by
    simpa [prefixWord, tailWord_294617, baseEnd_294617] using wordTrace_append hprefix tailTrace_294617
  have hstable : (prefixWord ++ tailWord_294617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294617).length < 2 ^ (prefixWord ++ tailWord_294617).sum := by decide
  have hdescent : baseEnd_294617 < baseStart_294617 := by decide
  rcases family_descends (prefixWord ++ tailWord_294617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294674 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 8]
def baseStart_294674 : Nat := 118140960795 + 294674 * 2 ^ 59
def prefixEnd_294674 : Nat := 4983230072969 + 3 ^ 40 * 294674 * 2
def baseEnd_294674 : Nat := 16812155375898368924425

theorem tailTrace_294674 : CollatzResearch.WordTrace tailWord_294674 prefixEnd_294674 16812155375898368924425 := by
  unfold tailWord_294674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2686910933613474789406769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7165095822969266105084717 2686910933613474789406769)
  ·
    refine ⟨2015183200210106092055077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2686910933613474789406769 2015183200210106092055077)
    ·
      refine ⟨377846850039394892260327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2015183200210106092055077 377846850039394892260327)
      ·
        refine ⟨566770275059092338390491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377846850039394892260327 566770275059092338390491)
        ·
          refine ⟨850155412588638507585737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566770275059092338390491 850155412588638507585737)
          ·
            refine ⟨637616559441478880689303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 850155412588638507585737 637616559441478880689303)
            ·
              refine ⟨956424839162218321033955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637616559441478880689303 956424839162218321033955)
              ·
                refine ⟨1434637258743327481550933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956424839162218321033955 1434637258743327481550933)
                ·
                  refine ⟨16812155375898368924425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1434637258743327481550933 16812155375898368924425)
                  ·
                    rfl

theorem cell23_294674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_294674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294674 prefixEnd_294674 := by exact prefixLift 294674
  have htrace : WordTrace (prefixWord ++ tailWord_294674) baseStart_294674 baseEnd_294674 := by
    simpa [prefixWord, tailWord_294674, baseEnd_294674] using wordTrace_append hprefix tailTrace_294674
  have hstable : (prefixWord ++ tailWord_294674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294674).length < 2 ^ (prefixWord ++ tailWord_294674).sum := by decide
  have hdescent : baseEnd_294674 < baseStart_294674 := by decide
  rcases family_descends (prefixWord ++ tailWord_294674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294727 : List Nat := [1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_294727 : Nat := 118140960795 + 294727 * 2 ^ 59
def prefixEnd_294727 : Nat := 4983230072969 + 3 ^ 40 * 294727 * 2
def baseEnd_294727 : Nat := 151336612857773612957081

theorem tailTrace_294727 : CollatzResearch.WordTrace tailWord_294727 prefixEnd_294727 151336612857773612957081 := by
  unfold tailWord_294727
  simp only [CollatzResearch.WordTrace]
  refine ⟨10749576803261889209306435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7166384535507926139537623 10749576803261889209306435)
  ·
    refine ⟨16124365204892833813959653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10749576803261889209306435 16124365204892833813959653)
    ·
      refine ⟨3023318475917406340117435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16124365204892833813959653 3023318475917406340117435)
      ·
        refine ⟨4534977713876109510176153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3023318475917406340117435 4534977713876109510176153)
        ·
          refine ⟨3401233285407082132632115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4534977713876109510176153 3401233285407082132632115)
          ·
            refine ⟨5101849928110623198948173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3401233285407082132632115 5101849928110623198948173)
            ·
              refine ⟨1913193723041483699605565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5101849928110623198948173 1913193723041483699605565)
              ·
                refine ⟨717447646140556387352087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1913193723041483699605565 717447646140556387352087)
                ·
                  refine ⟨1076171469210834581028131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717447646140556387352087 1076171469210834581028131)
                  ·
                    refine ⟨1614257203816251871542197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1076171469210834581028131 1614257203816251871542197)
                    ·
                      refine ⟨151336612857773612957081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1614257203816251871542197 151336612857773612957081)
                      ·
                        rfl

theorem cell23_294727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_294727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294727 prefixEnd_294727 := by exact prefixLift 294727
  have htrace : WordTrace (prefixWord ++ tailWord_294727) baseStart_294727 baseEnd_294727 := by
    simpa [prefixWord, tailWord_294727, baseEnd_294727] using wordTrace_append hprefix tailTrace_294727
  have hstable : (prefixWord ++ tailWord_294727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294727).length < 2 ^ (prefixWord ++ tailWord_294727).sum := by decide
  have hdescent : baseEnd_294727 < baseStart_294727 := by decide
  rcases family_descends (prefixWord ++ tailWord_294727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294737 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 1, 1, 6]
def baseStart_294737 : Nat := 118140960795 + 294737 * 2 ^ 59
def prefixEnd_294737 : Nat := 4983230072969 + 3 ^ 40 * 294737 * 2
def baseEnd_294737 : Nat := 151341747664318573832035

theorem tailTrace_294737 : CollatzResearch.WordTrace tailWord_294737 prefixEnd_294737 151341747664318573832035 := by
  unfold tailWord_294737
  simp only [CollatzResearch.WordTrace]
  refine ⟨10749941533225660917170465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7166627688817107278113643 10749941533225660917170465)
  ·
    refine ⟨8062456149919245687877849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10749941533225660917170465 8062456149919245687877849)
    ·
      refine ⟨6046842112439434265908387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8062456149919245687877849 6046842112439434265908387)
      ·
        refine ⟨9070263168659151398862581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6046842112439434265908387 9070263168659151398862581)
        ·
          refine ⟨850337172061795443643367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9070263168659151398862581 850337172061795443643367)
          ·
            refine ⟨1275505758092693165465051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850337172061795443643367 1275505758092693165465051)
            ·
              refine ⟨1913258637139039748197577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1275505758092693165465051 1913258637139039748197577)
              ·
                refine ⟨1434943977854279811148183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1913258637139039748197577 1434943977854279811148183)
                ·
                  refine ⟨2152415966781419716722275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434943977854279811148183 2152415966781419716722275)
                  ·
                    refine ⟨3228623950172129575083413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2152415966781419716722275 3228623950172129575083413)
                    ·
                      refine ⟨151341747664318573832035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3228623950172129575083413 151341747664318573832035)
                      ·
                        rfl

theorem cell23_294737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_294737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294737 prefixEnd_294737 := by exact prefixLift 294737
  have htrace : WordTrace (prefixWord ++ tailWord_294737) baseStart_294737 baseEnd_294737 := by
    simpa [prefixWord, tailWord_294737, baseEnd_294737] using wordTrace_append hprefix tailTrace_294737
  have hstable : (prefixWord ++ tailWord_294737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294737).length < 2 ^ (prefixWord ++ tailWord_294737).sum := by decide
  have hdescent : baseEnd_294737 < baseStart_294737 := by decide
  rcases family_descends (prefixWord ++ tailWord_294737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294751 : List Nat := [1, 1, 2, 3, 1, 4, 4, 1, 2, 4]
def baseStart_294751 : Nat := 118140960795 + 294751 * 2 ^ 59
def prefixEnd_294751 : Nat := 4983230072969 + 3 ^ 40 * 294751 * 2
def baseEnd_294751 : Nat := 50449645464493839685657

theorem tailTrace_294751 : CollatzResearch.WordTrace tailWord_294751 prefixEnd_294751 50449645464493839685657 := by
  unfold tailWord_294751
  simp only [CollatzResearch.WordTrace]
  refine ⟨10750452155174941308180107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7166968103449960872120071 10750452155174941308180107)
  ·
    refine ⟨16125678232762411962270161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10750452155174941308180107 16125678232762411962270161)
    ·
      refine ⟨12094258674571808971702621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16125678232762411962270161 12094258674571808971702621)
      ·
        refine ⟨4535347002964428364388483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12094258674571808971702621 4535347002964428364388483)
        ·
          refine ⟨6803020504446642546582725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4535347002964428364388483 6803020504446642546582725)
          ·
            refine ⟨1275566344583745477484261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6803020504446642546582725 1275566344583745477484261)
            ·
              refine ⟨239168689609452277028299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1275566344583745477484261 239168689609452277028299)
              ·
                refine ⟨358753034414178415542449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239168689609452277028299 358753034414178415542449)
                ·
                  refine ⟨269064775810633811656837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 358753034414178415542449 269064775810633811656837)
                  ·
                    refine ⟨50449645464493839685657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 269064775810633811656837 50449645464493839685657)
                    ·
                      rfl

theorem cell23_294751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 2, 4].length) (baseStart_294751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294751 prefixEnd_294751 := by exact prefixLift 294751
  have htrace : WordTrace (prefixWord ++ tailWord_294751) baseStart_294751 baseEnd_294751 := by
    simpa [prefixWord, tailWord_294751, baseEnd_294751] using wordTrace_append hprefix tailTrace_294751
  have hstable : (prefixWord ++ tailWord_294751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294751).length < 2 ^ (prefixWord ++ tailWord_294751).sum := by decide
  have hdescent : baseEnd_294751 < baseStart_294751 := by decide
  rcases family_descends (prefixWord ++ tailWord_294751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294754 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_294754 : Nat := 118140960795 + 294754 * 2 ^ 59
def prefixEnd_294754 : Nat := 4983230072969 + 3 ^ 40 * 294754 * 2
def baseEnd_294754 : Nat := 151350476835445007319457

theorem tailTrace_294754 : CollatzResearch.WordTrace tailWord_294754 prefixEnd_294754 151350476835445007319457 := by
  unfold tailWord_294754
  simp only [CollatzResearch.WordTrace]
  refine ⟨2687640393541018205134829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7167041049442715213692877 2687640393541018205134829)
  ·
    refine ⟨1007865147577881826925561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2687640393541018205134829 1007865147577881826925561)
    ·
      refine ⟨755898860683411370194171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1007865147577881826925561 755898860683411370194171)
      ·
        refine ⟨1133848291025117055291257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 755898860683411370194171 1133848291025117055291257)
        ·
          refine ⟨850386218268837791468443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1133848291025117055291257 850386218268837791468443)
          ·
            refine ⟨1275579327403256687202665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850386218268837791468443 1275579327403256687202665)
            ·
              refine ⟨956684495552442515401999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1275579327403256687202665 956684495552442515401999)
              ·
                refine ⟨1435026743328663773102999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956684495552442515401999 1435026743328663773102999)
                ·
                  refine ⟨2152540114992995659654499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1435026743328663773102999 2152540114992995659654499)
                  ·
                    refine ⟨3228810172489493489481749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2152540114992995659654499 3228810172489493489481749)
                    ·
                      refine ⟨151350476835445007319457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3228810172489493489481749 151350476835445007319457)
                      ·
                        rfl

theorem cell23_294754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_294754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294754 prefixEnd_294754 := by exact prefixLift 294754
  have htrace : WordTrace (prefixWord ++ tailWord_294754) baseStart_294754 baseEnd_294754 := by
    simpa [prefixWord, tailWord_294754, baseEnd_294754] using wordTrace_append hprefix tailTrace_294754
  have hstable : (prefixWord ++ tailWord_294754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294754).length < 2 ^ (prefixWord ++ tailWord_294754).sum := by decide
  have hdescent : baseEnd_294754 < baseStart_294754 := by decide
  rcases family_descends (prefixWord ++ tailWord_294754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294798 : List Nat := [4, 1, 1, 5, 2, 1, 1, 8]
def baseStart_294798 : Nat := 118140960795 + 294798 * 2 ^ 59
def prefixEnd_294798 : Nat := 4983230072969 + 3 ^ 40 * 294798 * 2
def baseEnd_294798 : Nat := 5606409999416401302565

theorem tailTrace_294798 : CollatzResearch.WordTrace tailWord_294798 prefixEnd_294798 5606409999416401302565 := by
  unfold tailWord_294798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1344020798250583541892631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7168110924003112223427365 1344020798250583541892631)
  ·
    refine ⟨2016031197375875312838947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1344020798250583541892631 2016031197375875312838947)
    ·
      refine ⟨3024046796063812969258421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2016031197375875312838947 3024046796063812969258421)
      ·
        refine ⟨283504387130982465867977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3024046796063812969258421 283504387130982465867977)
        ·
          refine ⟨212628290348236849400983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283504387130982465867977 212628290348236849400983)
          ·
            refine ⟨318942435522355274101475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212628290348236849400983 318942435522355274101475)
            ·
              refine ⟨478413653283532911152213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318942435522355274101475 478413653283532911152213)
              ·
                refine ⟨5606409999416401302565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 478413653283532911152213 5606409999416401302565)
                ·
                  rfl

theorem cell23_294798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 8].length) (baseStart_294798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294798 prefixEnd_294798 := by exact prefixLift 294798
  have htrace : WordTrace (prefixWord ++ tailWord_294798) baseStart_294798 baseEnd_294798 := by
    simpa [prefixWord, tailWord_294798, baseEnd_294798] using wordTrace_append hprefix tailTrace_294798
  have hstable : (prefixWord ++ tailWord_294798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294798).length < 2 ^ (prefixWord ++ tailWord_294798).sum := by decide
  have hdescent : baseEnd_294798 < baseStart_294798 := by decide
  rcases family_descends (prefixWord ++ tailWord_294798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294807 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 1, 8]
def baseStart_294807 : Nat := 118140960795 + 294807 * 2 ^ 59
def prefixEnd_294807 : Nat := 4983230072969 + 3 ^ 40 * 294807 * 2
def baseEnd_294807 : Nat := 50459230436711099985571

theorem tailTrace_294807 : CollatzResearch.WordTrace tailWord_294807 prefixEnd_294807 50459230436711099985571 := by
  unfold tailWord_294807
  simp only [CollatzResearch.WordTrace]
  refine ⟨10752494642972062872218675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7168329761981375248145783 10752494642972062872218675)
  ·
    refine ⟨16128741964458094308328013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10752494642972062872218675 16128741964458094308328013)
    ·
      refine ⟨6048278236671785365623005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16128741964458094308328013 6048278236671785365623005)
      ·
        refine ⟨2268104338751919512108627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6048278236671785365623005 2268104338751919512108627)
        ·
          refine ⟨3402156508127879268162941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2268104338751919512108627 3402156508127879268162941)
          ·
            refine ⟨1275808690547954725561103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3402156508127879268162941 1275808690547954725561103)
            ·
              refine ⟨1913713035821932088341655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1275808690547954725561103 1913713035821932088341655)
              ·
                refine ⟨2870569553732898132512483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1913713035821932088341655 2870569553732898132512483)
                ·
                  refine ⟨4305854330599347198768725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2870569553732898132512483 4305854330599347198768725)
                  ·
                    refine ⟨50459230436711099985571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4305854330599347198768725 50459230436711099985571)
                    ·
                      rfl

theorem cell23_294807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_294807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294807 prefixEnd_294807 := by exact prefixLift 294807
  have htrace : WordTrace (prefixWord ++ tailWord_294807) baseStart_294807 baseEnd_294807 := by
    simpa [prefixWord, tailWord_294807, baseEnd_294807] using wordTrace_append hprefix tailTrace_294807
  have hstable : (prefixWord ++ tailWord_294807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294807).length < 2 ^ (prefixWord ++ tailWord_294807).sum := by decide
  have hdescent : baseEnd_294807 < baseStart_294807 := by decide
  rcases family_descends (prefixWord ++ tailWord_294807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294808 : List Nat := [2, 1, 2, 6, 1, 1, 2, 1, 1, 3, 3]
def baseStart_294808 : Nat := 118140960795 + 294808 * 2 ^ 59
def prefixEnd_294808 : Nat := 4983230072969 + 3 ^ 40 * 294808 * 2
def baseEnd_294808 : Nat := 151378204790787796044209

theorem tailTrace_294808 : CollatzResearch.WordTrace tailWord_294808 prefixEnd_294808 151378204790787796044209 := by
  unfold tailWord_294808
  simp only [CollatzResearch.WordTrace]
  refine ⟨5376265557984220021502539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7168354077312293362003385 5376265557984220021502539)
  ·
    refine ⟨8064398336976330032253809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5376265557984220021502539 8064398336976330032253809)
    ·
      refine ⟨6048298752732247524190357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8064398336976330032253809 6048298752732247524190357)
      ·
        refine ⟨283514004034324102696423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6048298752732247524190357 283514004034324102696423)
        ·
          refine ⟨425271006051486154044635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283514004034324102696423 425271006051486154044635)
          ·
            refine ⟨637906509077229231066953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425271006051486154044635 637906509077229231066953)
            ·
              refine ⟨478429881807921923300215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 637906509077229231066953 478429881807921923300215)
              ·
                refine ⟨717644822711882884950323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478429881807921923300215 717644822711882884950323)
                ·
                  refine ⟨1076467234067824327425485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717644822711882884950323 1076467234067824327425485)
                  ·
                    refine ⟨403675212775434122784557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1076467234067824327425485 403675212775434122784557)
                    ·
                      refine ⟨151378204790787796044209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 403675212775434122784557 151378204790787796044209)
                      ·
                        rfl

theorem cell23_294808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_294808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294808 prefixEnd_294808 := by exact prefixLift 294808
  have htrace : WordTrace (prefixWord ++ tailWord_294808) baseStart_294808 baseEnd_294808 := by
    simpa [prefixWord, tailWord_294808, baseEnd_294808] using wordTrace_append hprefix tailTrace_294808
  have hstable : (prefixWord ++ tailWord_294808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294808).length < 2 ^ (prefixWord ++ tailWord_294808).sum := by decide
  have hdescent : baseEnd_294808 < baseStart_294808 := by decide
  rcases family_descends (prefixWord ++ tailWord_294808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294827 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 4]
def baseStart_294827 : Nat := 118140960795 + 294827 * 2 ^ 59
def prefixEnd_294827 : Nat := 4983230072969 + 3 ^ 40 * 294827 * 2
def baseEnd_294827 : Nat := 151387960923223221706621

theorem tailTrace_294827 : CollatzResearch.WordTrace tailWord_294827 prefixEnd_294827 151387960923223221706621 := by
  unfold tailWord_294827
  simp only [CollatzResearch.WordTrace]
  refine ⟨10753224102899606287946735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7168816068599737525297823 10753224102899606287946735)
  ·
    refine ⟨16129836154349409431920103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10753224102899606287946735 16129836154349409431920103)
    ·
      refine ⟨24194754231524114147880155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16129836154349409431920103 24194754231524114147880155)
      ·
        refine ⟨36292131347286171221820233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24194754231524114147880155 36292131347286171221820233)
        ·
          refine ⟨27219098510464628416365175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36292131347286171221820233 27219098510464628416365175)
          ·
            refine ⟨40828647765696942624547763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27219098510464628416365175 40828647765696942624547763)
            ·
              refine ⟨61242971648545413936821645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40828647765696942624547763 61242971648545413936821645)
              ·
                refine ⟨22966114368204530226308117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61242971648545413936821645 22966114368204530226308117)
                ·
                  refine ⟨1076536611009587354358193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22966114368204530226308117 1076536611009587354358193)
                  ·
                    refine ⟨807402458257190515768645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1076536611009587354358193 807402458257190515768645)
                    ·
                      refine ⟨151387960923223221706621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 807402458257190515768645 151387960923223221706621)
                      ·
                        rfl

theorem cell23_294827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 4].length) (baseStart_294827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294827 prefixEnd_294827 := by exact prefixLift 294827
  have htrace : WordTrace (prefixWord ++ tailWord_294827) baseStart_294827 baseEnd_294827 := by
    simpa [prefixWord, tailWord_294827, baseEnd_294827] using wordTrace_append hprefix tailTrace_294827
  have hstable : (prefixWord ++ tailWord_294827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294827).length < 2 ^ (prefixWord ++ tailWord_294827).sum := by decide
  have hdescent : baseEnd_294827 < baseStart_294827 := by decide
  rcases family_descends (prefixWord ++ tailWord_294827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294831 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 4, 2, 2]
def baseStart_294831 : Nat := 118140960795 + 294831 * 2 ^ 59
def prefixEnd_294831 : Nat := 4983230072969 + 3 ^ 40 * 294831 * 2
def baseEnd_294831 : Nat := 151390014845841206056603

theorem tailTrace_294831 : CollatzResearch.WordTrace tailWord_294831 prefixEnd_294831 151390014845841206056603 := by
  unfold tailWord_294831
  simp only [CollatzResearch.WordTrace]
  refine ⟨10753369994885114971092347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7168913329923409980728231 10753369994885114971092347)
  ·
    refine ⟨16130054992327672456638521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10753369994885114971092347 16130054992327672456638521)
    ·
      refine ⟨12097541244245754342478891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16130054992327672456638521 12097541244245754342478891)
      ·
        refine ⟨18146311866368631513718337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12097541244245754342478891 18146311866368631513718337)
        ·
          refine ⟨13609733899776473635288753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18146311866368631513718337 13609733899776473635288753)
          ·
            refine ⟨10207300424832355226466565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13609733899776473635288753 10207300424832355226466565)
            ·
              refine ⟨1913868829656066604962481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10207300424832355226466565 1913868829656066604962481)
              ·
                refine ⟨1435401622242049953721861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1913868829656066604962481 1435401622242049953721861)
                ·
                  refine ⟨269137804170384366322849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1435401622242049953721861 269137804170384366322849)
                  ·
                    refine ⟨201853353127788274742137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 269137804170384366322849 201853353127788274742137)
                    ·
                      refine ⟨151390014845841206056603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 201853353127788274742137 151390014845841206056603)
                      ·
                        rfl

theorem cell23_294831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 2, 2].length) (baseStart_294831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294831 prefixEnd_294831 := by exact prefixLift 294831
  have htrace : WordTrace (prefixWord ++ tailWord_294831) baseStart_294831 baseEnd_294831 := by
    simpa [prefixWord, tailWord_294831, baseEnd_294831] using wordTrace_append hprefix tailTrace_294831
  have hstable : (prefixWord ++ tailWord_294831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294831).length < 2 ^ (prefixWord ++ tailWord_294831).sum := by decide
  have hdescent : baseEnd_294831 < baseStart_294831 := by decide
  rcases family_descends (prefixWord ++ tailWord_294831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294864 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 3]
def baseStart_294864 : Nat := 118140960795 + 294864 * 2 ^ 59
def prefixEnd_294864 : Nat := 4983230072969 + 3 ^ 40 * 294864 * 2
def baseEnd_294864 : Nat := 151406959707439576943951

theorem tailTrace_294864 : CollatzResearch.WordTrace tailWord_294864 prefixEnd_294864 151406959707439576943951 := by
  unfold tailWord_294864
  simp only [CollatzResearch.WordTrace]
  refine ⟨5377286801882780803521823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7169715735843707738029097 5377286801882780803521823)
  ·
    refine ⟨8065930202824171205282735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5377286801882780803521823 8065930202824171205282735)
    ·
      refine ⟨12098895304236256807924103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8065930202824171205282735 12098895304236256807924103)
      ·
        refine ⟨18148342956354385211886155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12098895304236256807924103 18148342956354385211886155)
        ·
          refine ⟨27222514434531577817829233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18148342956354385211886155 27222514434531577817829233)
          ·
            refine ⟨20416885825898683363371925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27222514434531577817829233 20416885825898683363371925)
            ·
              refine ⟨957041523089000782658059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20416885825898683363371925 957041523089000782658059)
              ·
                refine ⟨1435562284633501173987089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957041523089000782658059 1435562284633501173987089)
                ·
                  refine ⟨1076671713475125880490317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1435562284633501173987089 1076671713475125880490317)
                  ·
                    refine ⟨403751892553172205183869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1076671713475125880490317 403751892553172205183869)
                    ·
                      refine ⟨151406959707439576943951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 403751892553172205183869 151406959707439576943951)
                      ·
                        rfl

theorem cell23_294864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 3].length) (baseStart_294864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294864 prefixEnd_294864 := by exact prefixLift 294864
  have htrace : WordTrace (prefixWord ++ tailWord_294864) baseStart_294864 baseEnd_294864 := by
    simpa [prefixWord, tailWord_294864, baseEnd_294864] using wordTrace_append hprefix tailTrace_294864
  have hstable : (prefixWord ++ tailWord_294864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294864).length < 2 ^ (prefixWord ++ tailWord_294864).sum := by decide
  have hdescent : baseEnd_294864 < baseStart_294864 := by decide
  rcases family_descends (prefixWord ++ tailWord_294864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294884 : List Nat := [2, 3, 1, 1, 1, 1, 4, 3, 2, 5]
def baseStart_294884 : Nat := 118140960795 + 294884 * 2 ^ 59
def prefixEnd_294884 : Nat := 4983230072969 + 3 ^ 40 * 294884 * 2
def baseEnd_294884 : Nat := 50472409773509832897953

theorem tailTrace_294884 : CollatzResearch.WordTrace tailWord_294884 prefixEnd_294884 50472409773509832897953 := by
  unfold tailWord_294884
  simp only [CollatzResearch.WordTrace]
  refine ⟨5377651531846552511385853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7170202042462070015181137 5377651531846552511385853)
  ·
    refine ⟨2016619324442457191769695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5377651531846552511385853 2016619324442457191769695)
    ·
      refine ⟨3024928986663685787654543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2016619324442457191769695 3024928986663685787654543)
      ·
        refine ⟨4537393479995528681481815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3024928986663685787654543 4537393479995528681481815)
        ·
          refine ⟨6806090219993293022222723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4537393479995528681481815 6806090219993293022222723)
          ·
            refine ⟨10209135329989939533334085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6806090219993293022222723 10209135329989939533334085)
            ·
              refine ⟨1914212874373113662500141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10209135329989939533334085 1914212874373113662500141)
              ·
                refine ⟨717829827889917623437553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1914212874373113662500141 717829827889917623437553)
                ·
                  refine ⟨538372370917438217578165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 717829827889917623437553 538372370917438217578165)
                  ·
                    refine ⟨50472409773509832897953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 538372370917438217578165 50472409773509832897953)
                    ·
                      rfl

theorem cell23_294884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_294884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294884 prefixEnd_294884 := by exact prefixLift 294884
  have htrace : WordTrace (prefixWord ++ tailWord_294884) baseStart_294884 baseEnd_294884 := by
    simpa [prefixWord, tailWord_294884, baseEnd_294884] using wordTrace_append hprefix tailTrace_294884
  have hstable : (prefixWord ++ tailWord_294884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294884).length < 2 ^ (prefixWord ++ tailWord_294884).sum := by decide
  have hdescent : baseEnd_294884 < baseStart_294884 := by decide
  rcases family_descends (prefixWord ++ tailWord_294884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294904 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 4, 1, 4]
def baseStart_294904 : Nat := 118140960795 + 294904 * 2 ^ 59
def prefixEnd_294904 : Nat := 4983230072969 + 3 ^ 40 * 294904 * 2
def baseEnd_294904 : Nat := 151427498933619420443767

theorem tailTrace_294904 : CollatzResearch.WordTrace tailWord_294904 prefixEnd_294904 151427498933619420443767 := by
  unfold tailWord_294904
  simp only [CollatzResearch.WordTrace]
  refine ⟨5378016261810324219249883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7170688349080432292333177 5378016261810324219249883)
  ·
    refine ⟨8067024392715486328874825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5378016261810324219249883 8067024392715486328874825)
    ·
      refine ⟨6050268294536614746656119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8067024392715486328874825 6050268294536614746656119)
      ·
        refine ⟨9075402441804922119984179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6050268294536614746656119 9075402441804922119984179)
        ·
          refine ⟨13613103662707383179976269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9075402441804922119984179 13613103662707383179976269)
          ·
            refine ⟨5104913873515268692491101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13613103662707383179976269 5104913873515268692491101)
            ·
              refine ⟨1914342702568225759684163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5104913873515268692491101 1914342702568225759684163)
              ·
                refine ⟨2871514053852338639526245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1914342702568225759684163 2871514053852338639526245)
                ·
                  refine ⟨538408885097313494911171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2871514053852338639526245 538408885097313494911171)
                  ·
                    refine ⟨807613327645970242366757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 538408885097313494911171 807613327645970242366757)
                    ·
                      refine ⟨151427498933619420443767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 807613327645970242366757 151427498933619420443767)
                      ·
                        rfl

theorem cell23_294904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_294904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294904 prefixEnd_294904 := by exact prefixLift 294904
  have htrace : WordTrace (prefixWord ++ tailWord_294904) baseStart_294904 baseEnd_294904 := by
    simpa [prefixWord, tailWord_294904, baseEnd_294904] using wordTrace_append hprefix tailTrace_294904
  have hstable : (prefixWord ++ tailWord_294904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294904).length < 2 ^ (prefixWord ++ tailWord_294904).sum := by decide
  have hdescent : baseEnd_294904 < baseStart_294904 := by decide
  rcases family_descends (prefixWord ++ tailWord_294904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294916 : List Nat := [2, 3, 2, 4, 2, 1, 2, 1, 2, 2, 2]
def baseStart_294916 : Nat := 118140960795 + 294916 * 2 ^ 59
def prefixEnd_294916 : Nat := 4983230072969 + 3 ^ 40 * 294916 * 2
def baseEnd_294916 : Nat := 151433660701473373493713

theorem tailTrace_294916 : CollatzResearch.WordTrace tailWord_294916 prefixEnd_294916 151433660701473373493713 := by
  unfold tailWord_294916
  simp only [CollatzResearch.WordTrace]
  refine ⟨5378235099788587243968301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7170980133051449658624401 5378235099788587243968301)
  ·
    refine ⟨2016838162420720216488113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5378235099788587243968301 2016838162420720216488113)
    ·
      refine ⟨1512628621815540162366085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2016838162420720216488113 1512628621815540162366085)
      ·
        refine ⟨283617866590413780443641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1512628621815540162366085 283617866590413780443641)
        ·
          refine ⟨212713399942810335332731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283617866590413780443641 212713399942810335332731)
          ·
            refine ⟨319070099914215502999097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212713399942810335332731 319070099914215502999097)
            ·
              refine ⟨239302574935661627249323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319070099914215502999097 239302574935661627249323)
              ·
                refine ⟨358953862403492440873985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239302574935661627249323 358953862403492440873985)
                ·
                  refine ⟨269215396802619330655489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 358953862403492440873985 269215396802619330655489)
                  ·
                    refine ⟨201911547601964497991617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 269215396802619330655489 201911547601964497991617)
                    ·
                      refine ⟨151433660701473373493713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 201911547601964497991617 151433660701473373493713)
                      ·
                        rfl

theorem cell23_294916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_294916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294916 prefixEnd_294916 := by exact prefixLift 294916
  have htrace : WordTrace (prefixWord ++ tailWord_294916) baseStart_294916 baseEnd_294916 := by
    simpa [prefixWord, tailWord_294916, baseEnd_294916] using wordTrace_append hprefix tailTrace_294916
  have hstable : (prefixWord ++ tailWord_294916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294916).length < 2 ^ (prefixWord ++ tailWord_294916).sum := by decide
  have hdescent : baseEnd_294916 < baseStart_294916 := by decide
  rcases family_descends (prefixWord ++ tailWord_294916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294958 : List Nat := [4, 1, 3, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_294958 : Nat := 118140960795 + 294958 * 2 ^ 59
def prefixEnd_294958 : Nat := 4983230072969 + 3 ^ 40 * 294958 * 2
def baseEnd_294958 : Nat := 151455226888962209168519

theorem tailTrace_294958 : CollatzResearch.WordTrace tailWord_294958 prefixEnd_294958 151455226888962209168519 := by
  unfold tailWord_294958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1344750258178126957620691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7172001376950010440643685 1344750258178126957620691)
  ·
    refine ⟨2017125387267190436431037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1344750258178126957620691 2017125387267190436431037)
    ·
      refine ⟨756422020225196413661639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2017125387267190436431037 756422020225196413661639)
      ·
        refine ⟨1134633030337794620492459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 756422020225196413661639 1134633030337794620492459)
        ·
          refine ⟨1701949545506691930738689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1134633030337794620492459 1701949545506691930738689)
          ·
            refine ⟨1276462159130018948054017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1701949545506691930738689 1276462159130018948054017)
            ·
              refine ⟨957346619347514211040513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1276462159130018948054017 957346619347514211040513)
              ·
                refine ⟨718009964510635658280385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 957346619347514211040513 718009964510635658280385)
                ·
                  refine ⟨538507473382976743710289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 718009964510635658280385 538507473382976743710289)
                  ·
                    refine ⟨403880605037232557782717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 538507473382976743710289 403880605037232557782717)
                    ·
                      refine ⟨151455226888962209168519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 403880605037232557782717 151455226888962209168519)
                      ·
                        rfl

theorem cell23_294958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_294958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294958 prefixEnd_294958 := by exact prefixLift 294958
  have htrace : WordTrace (prefixWord ++ tailWord_294958) baseStart_294958 baseEnd_294958 := by
    simpa [prefixWord, tailWord_294958, baseEnd_294958] using wordTrace_append hprefix tailTrace_294958
  have hstable : (prefixWord ++ tailWord_294958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294958).length < 2 ^ (prefixWord ++ tailWord_294958).sum := by decide
  have hdescent : baseEnd_294958 < baseStart_294958 := by decide
  rcases family_descends (prefixWord ++ tailWord_294958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294961 : List Nat := [1, 2, 2, 3, 1, 4, 2, 2, 6]
def baseStart_294961 : Nat := 118140960795 + 294961 * 2 ^ 59
def prefixEnd_294961 : Nat := 4983230072969 + 3 ^ 40 * 294961 * 2
def baseEnd_294961 : Nat := 16828529703436188603445

theorem tailTrace_294961 : CollatzResearch.WordTrace tailWord_294961 prefixEnd_294961 16828529703436188603445 := by
  unfold tailWord_294961
  simp only [CollatzResearch.WordTrace]
  refine ⟨10758111484414147173324737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7172074322942764782216491 10758111484414147173324737)
  ·
    refine ⟨8068583613310610379993553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10758111484414147173324737 8068583613310610379993553)
    ·
      refine ⟨6051437709982957784995165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8068583613310610379993553 6051437709982957784995165)
      ·
        refine ⟨2269289141243609169373187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6051437709982957784995165 2269289141243609169373187)
        ·
          refine ⟨3403933711865413754059781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2269289141243609169373187 3403933711865413754059781)
          ·
            refine ⟨638237570974765078886209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3403933711865413754059781 638237570974765078886209)
            ·
              refine ⟨478678178231073809164657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 638237570974765078886209 478678178231073809164657)
              ·
                refine ⟨359008633673305356873493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 478678178231073809164657 359008633673305356873493)
                ·
                  refine ⟨16828529703436188603445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 359008633673305356873493 16828529703436188603445)
                  ·
                    rfl

theorem cell23_294961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 6].length) (baseStart_294961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294961 prefixEnd_294961 := by exact prefixLift 294961
  have htrace : WordTrace (prefixWord ++ tailWord_294961) baseStart_294961 baseEnd_294961 := by
    simpa [prefixWord, tailWord_294961, baseEnd_294961] using wordTrace_append hprefix tailTrace_294961
  have hstable : (prefixWord ++ tailWord_294961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294961).length < 2 ^ (prefixWord ++ tailWord_294961).sum := by decide
  have hdescent : baseEnd_294961 < baseStart_294961 := by decide
  rcases family_descends (prefixWord ++ tailWord_294961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294965 : List Nat := [1, 3, 3, 1, 1, 1, 6, 2, 1, 4]
def baseStart_294965 : Nat := 118140960795 + 294965 * 2 ^ 59
def prefixEnd_294965 : Nat := 4983230072969 + 3 ^ 40 * 294965 * 2
def baseEnd_294965 : Nat := 50486273751181227260329

theorem tailTrace_294965 : CollatzResearch.WordTrace tailWord_294965 prefixEnd_294965 50486273751181227260329 := by
  unfold tailWord_294965
  simp only [CollatzResearch.WordTrace]
  refine ⟨10758257376399655856470349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7172171584266437237646899 10758257376399655856470349)
  ·
    refine ⟨4034346516149870946176381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10758257376399655856470349 4034346516149870946176381)
    ·
      refine ⟨1512879943556201604816143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4034346516149870946176381 1512879943556201604816143)
      ·
        refine ⟨2269319915334302407224215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1512879943556201604816143 2269319915334302407224215)
        ·
          refine ⟨3403979873001453610836323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2269319915334302407224215 3403979873001453610836323)
          ·
            refine ⟨5105969809502180416254485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3403979873001453610836323 5105969809502180416254485)
            ·
              refine ⟨239342334820414707011929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5105969809502180416254485 239342334820414707011929)
              ·
                refine ⟨179506751115311030258947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239342334820414707011929 179506751115311030258947)
                ·
                  refine ⟨269260126672966545388421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179506751115311030258947 269260126672966545388421)
                  ·
                    refine ⟨50486273751181227260329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 269260126672966545388421 50486273751181227260329)
                    ·
                      rfl

theorem cell23_294965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_294965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294965 prefixEnd_294965 := by exact prefixLift 294965
  have htrace : WordTrace (prefixWord ++ tailWord_294965) baseStart_294965 baseEnd_294965 := by
    simpa [prefixWord, tailWord_294965, baseEnd_294965] using wordTrace_append hprefix tailTrace_294965
  have hstable : (prefixWord ++ tailWord_294965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294965).length < 2 ^ (prefixWord ++ tailWord_294965).sum := by decide
  have hdescent : baseEnd_294965 < baseStart_294965 := by decide
  rcases family_descends (prefixWord ++ tailWord_294965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294981 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 1, 5, 2]
def baseStart_294981 : Nat := 118140960795 + 294981 * 2 ^ 59
def prefixEnd_294981 : Nat := 4983230072969 + 3 ^ 40 * 294981 * 2
def baseEnd_294981 : Nat := 151467036944015619180913

theorem tailTrace_294981 : CollatzResearch.WordTrace tailWord_294981 prefixEnd_294981 151467036944015619180913 := by
  unfold tailWord_294981
  simp only [CollatzResearch.WordTrace]
  refine ⟨10758840944341690589052797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7172560629561127059368531 10758840944341690589052797)
  ·
    refine ⟨4034565354128133970894799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10758840944341690589052797 4034565354128133970894799)
    ·
      refine ⟨6051848031192200956342199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4034565354128133970894799 6051848031192200956342199)
      ·
        refine ⟨9077772046788301434513299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6051848031192200956342199 9077772046788301434513299)
        ·
          refine ⟨13616658070182452151769949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9077772046788301434513299 13616658070182452151769949)
          ·
            refine ⟨5106246776318419556913731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13616658070182452151769949 5106246776318419556913731)
            ·
              refine ⟨7659370164477629335370597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5106246776318419556913731 7659370164477629335370597)
              ·
                refine ⟨1436131905839555500381987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7659370164477629335370597 1436131905839555500381987)
                ·
                  refine ⟨2154197858759333250572981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1436131905839555500381987 2154197858759333250572981)
                  ·
                    refine ⟨201956049258687492241217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2154197858759333250572981 201956049258687492241217)
                    ·
                      refine ⟨151467036944015619180913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 201956049258687492241217 151467036944015619180913)
                      ·
                        rfl

theorem cell23_294981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 5, 2].length) (baseStart_294981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_294981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_294981 prefixEnd_294981 := by exact prefixLift 294981
  have htrace : WordTrace (prefixWord ++ tailWord_294981) baseStart_294981 baseEnd_294981 := by
    simpa [prefixWord, tailWord_294981, baseEnd_294981] using wordTrace_append hprefix tailTrace_294981
  have hstable : (prefixWord ++ tailWord_294981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294981).length < 2 ^ (prefixWord ++ tailWord_294981).sum := by decide
  have hdescent : baseEnd_294981 < baseStart_294981 := by decide
  rcases family_descends (prefixWord ++ tailWord_294981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295008 : List Nat := [2, 1, 1, 3, 2, 3, 4, 1, 1, 5]
def baseStart_295008 : Nat := 118140960795 + 295008 * 2 ^ 59
def prefixEnd_295008 : Nat := 4983230072969 + 3 ^ 40 * 295008 * 2
def baseEnd_295008 : Nat := 50493633640562337847763

theorem tailTrace_295008 : CollatzResearch.WordTrace tailWord_295008 prefixEnd_295008 50493633640562337847763 := by
  unfold tailWord_295008
  simp only [CollatzResearch.WordTrace]
  refine ⟨5379912857621937100142839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7173217143495916133523785 5379912857621937100142839)
  ·
    refine ⟨8069869286432905650214259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5379912857621937100142839 8069869286432905650214259)
    ·
      refine ⟨12104803929649358475321389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8069869286432905650214259 12104803929649358475321389)
      ·
        refine ⟨4539301473618509428245521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12104803929649358475321389 4539301473618509428245521)
        ·
          refine ⟨3404476105213882071184141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4539301473618509428245521 3404476105213882071184141)
          ·
            refine ⟨1276678539455205776694053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3404476105213882071184141 1276678539455205776694053)
            ·
              refine ⟨239377226147851083130135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1276678539455205776694053 239377226147851083130135)
              ·
                refine ⟨359065839221776624695203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239377226147851083130135 359065839221776624695203)
                ·
                  refine ⟨538598758832664937042805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 359065839221776624695203 538598758832664937042805)
                  ·
                    refine ⟨50493633640562337847763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 538598758832664937042805 50493633640562337847763)
                    ·
                      rfl

theorem cell23_295008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 1, 5].length) (baseStart_295008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295008 prefixEnd_295008 := by exact prefixLift 295008
  have htrace : WordTrace (prefixWord ++ tailWord_295008) baseStart_295008 baseEnd_295008 := by
    simpa [prefixWord, tailWord_295008, baseEnd_295008] using wordTrace_append hprefix tailTrace_295008
  have hstable : (prefixWord ++ tailWord_295008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295008).length < 2 ^ (prefixWord ++ tailWord_295008).sum := by decide
  have hdescent : baseEnd_295008 < baseStart_295008 := by decide
  rcases family_descends (prefixWord ++ tailWord_295008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295031 : List Nat := [1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 5]
def baseStart_295031 : Nat := 118140960795 + 295031 * 2 ^ 59
def prefixEnd_295031 : Nat := 4983230072969 + 3 ^ 40 * 295031 * 2
def baseEnd_295031 : Nat := 151492710976740423555683

theorem tailTrace_295031 : CollatzResearch.WordTrace tailWord_295031 prefixEnd_295031 151492710976740423555683 := by
  unfold tailWord_295031
  simp only [CollatzResearch.WordTrace]
  refine ⟨10760664594160549128372947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7173776396107032752248631 10760664594160549128372947)
  ·
    refine ⟨16140996891240823692559421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10760664594160549128372947 16140996891240823692559421)
    ·
      refine ⟨6052873834215308884709783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16140996891240823692559421 6052873834215308884709783)
      ·
        refine ⟨9079310751322963327064675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6052873834215308884709783 9079310751322963327064675)
        ·
          refine ⟨13618966126984444990597013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9079310751322963327064675 13618966126984444990597013)
          ·
            refine ⟨638389037202395858934235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13618966126984444990597013 638389037202395858934235)
            ·
              refine ⟨957583555803593788401353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638389037202395858934235 957583555803593788401353)
              ·
                refine ⟨718187666852695341301015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 957583555803593788401353 718187666852695341301015)
                ·
                  refine ⟨1077281500279043011951523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 718187666852695341301015 1077281500279043011951523)
                  ·
                    refine ⟨1615922250418564517927285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1077281500279043011951523 1615922250418564517927285)
                    ·
                      refine ⟨151492710976740423555683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1615922250418564517927285 151492710976740423555683)
                      ·
                        rfl

theorem cell23_295031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_295031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295031 prefixEnd_295031 := by exact prefixLift 295031
  have htrace : WordTrace (prefixWord ++ tailWord_295031) baseStart_295031 baseEnd_295031 := by
    simpa [prefixWord, tailWord_295031, baseEnd_295031] using wordTrace_append hprefix tailTrace_295031
  have hstable : (prefixWord ++ tailWord_295031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295031).length < 2 ^ (prefixWord ++ tailWord_295031).sum := by decide
  have hdescent : baseEnd_295031 < baseStart_295031 := by decide
  rcases family_descends (prefixWord ++ tailWord_295031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295045 : List Nat := [1, 3, 1, 1, 5, 1, 2, 2, 3, 2, 2]
def baseStart_295045 : Nat := 118140960795 + 295045 * 2 ^ 59
def prefixEnd_295045 : Nat := 4983230072969 + 3 ^ 40 * 295045 * 2
def baseEnd_295045 : Nat := 151499899705903368780619

theorem tailTrace_295045 : CollatzResearch.WordTrace tailWord_295045 prefixEnd_295045 151499899705903368780619 := by
  unfold tailWord_295045
  simp only [CollatzResearch.WordTrace]
  refine ⟨10761175216109829519382589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7174116810739886346255059 10761175216109829519382589)
  ·
    refine ⟨4035440706041186069768471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10761175216109829519382589 4035440706041186069768471)
    ·
      refine ⟨6053161059061779104652707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4035440706041186069768471 6053161059061779104652707)
      ·
        refine ⟨9079741588592668656979061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6053161059061779104652707 9079741588592668656979061)
        ·
          refine ⟨851225773930562686591787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9079741588592668656979061 851225773930562686591787)
          ·
            refine ⟨1276838660895844029887681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851225773930562686591787 1276838660895844029887681)
            ·
              refine ⟨957628995671883022415761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1276838660895844029887681 957628995671883022415761)
              ·
                refine ⟨718221746753912266811821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 957628995671883022415761 718221746753912266811821)
                ·
                  refine ⟨269333155032717100054433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718221746753912266811821 269333155032717100054433)
                  ·
                    refine ⟨201999866274537825040825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 269333155032717100054433 201999866274537825040825)
                    ·
                      refine ⟨151499899705903368780619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 201999866274537825040825 151499899705903368780619)
                      ·
                        rfl

theorem cell23_295045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 2, 2].length) (baseStart_295045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295045 prefixEnd_295045 := by exact prefixLift 295045
  have htrace : WordTrace (prefixWord ++ tailWord_295045) baseStart_295045 baseEnd_295045 := by
    simpa [prefixWord, tailWord_295045, baseEnd_295045] using wordTrace_append hprefix tailTrace_295045
  have hstable : (prefixWord ++ tailWord_295045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295045).length < 2 ^ (prefixWord ++ tailWord_295045).sum := by decide
  have hdescent : baseEnd_295045 < baseStart_295045 := by decide
  rcases family_descends (prefixWord ++ tailWord_295045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295061 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 3, 3, 3]
def baseStart_295061 : Nat := 118140960795 + 295061 * 2 ^ 59
def prefixEnd_295061 : Nat := 4983230072969 + 3 ^ 40 * 295061 * 2
def baseEnd_295061 : Nat := 151508115396375306180545

theorem tailTrace_295061 : CollatzResearch.WordTrace tailWord_295061 prefixEnd_295061 151508115396375306180545 := by
  unfold tailWord_295061
  simp only [CollatzResearch.WordTrace]
  refine ⟨10761758784051864251965037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7174505856034576167976691 10761758784051864251965037)
  ·
    refine ⟨4035659544019449094486889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10761758784051864251965037 4035659544019449094486889)
    ·
      refine ⟨3026744658014586820865167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4035659544019449094486889 3026744658014586820865167)
      ·
        refine ⟨4540116987021880231297751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3026744658014586820865167 4540116987021880231297751)
        ·
          refine ⟨6810175480532820346946627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4540116987021880231297751 6810175480532820346946627)
          ·
            refine ⟨10215263220799230520419941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6810175480532820346946627 10215263220799230520419941)
            ·
              refine ⟨1915361853899855722578739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10215263220799230520419941 1915361853899855722578739)
              ·
                refine ⟨2873042780849783583868109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1915361853899855722578739 2873042780849783583868109)
                ·
                  refine ⟨1077391042818668843950541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2873042780849783583868109 1077391042818668843950541)
                  ·
                    refine ⟨404021641057000816481453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1077391042818668843950541 404021641057000816481453)
                    ·
                      refine ⟨151508115396375306180545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 404021641057000816481453 151508115396375306180545)
                      ·
                        rfl

theorem cell23_295061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_295061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295061 prefixEnd_295061 := by exact prefixLift 295061
  have htrace : WordTrace (prefixWord ++ tailWord_295061) baseStart_295061 baseEnd_295061 := by
    simpa [prefixWord, tailWord_295061, baseEnd_295061] using wordTrace_append hprefix tailTrace_295061
  have hstable : (prefixWord ++ tailWord_295061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295061).length < 2 ^ (prefixWord ++ tailWord_295061).sum := by decide
  have hdescent : baseEnd_295061 < baseStart_295061 := by decide
  rcases family_descends (prefixWord ++ tailWord_295061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295079 : List Nat := [1, 1, 6, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_295079 : Nat := 118140960795 + 295079 * 2 ^ 59
def prefixEnd_295079 : Nat := 4983230072969 + 3 ^ 40 * 295079 * 2
def baseEnd_295079 : Nat := 151517358048156235755463

theorem tailTrace_295079 : CollatzResearch.WordTrace tailWord_295079 prefixEnd_295079 151517358048156235755463 := by
  unfold tailWord_295079
  simp only [CollatzResearch.WordTrace]
  refine ⟨10762415297986653326120291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7174943531991102217413527 10762415297986653326120291)
  ·
    refine ⟨16143622946979979989180437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10762415297986653326120291 16143622946979979989180437)
    ·
      refine ⟨756732325639686561992833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16143622946979979989180437 756732325639686561992833)
      ·
        refine ⟨567549244229764921494625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 756732325639686561992833 567549244229764921494625)
        ·
          refine ⟨425661933172323691120969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 567549244229764921494625 425661933172323691120969)
          ·
            refine ⟨319246449879242768340727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 425661933172323691120969 319246449879242768340727)
            ·
              refine ⟨478869674818864152511091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319246449879242768340727 478869674818864152511091)
              ·
                refine ⟨718304512228296228766637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478869674818864152511091 718304512228296228766637)
                ·
                  refine ⟨269364192085611085787489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718304512228296228766637 269364192085611085787489)
                  ·
                    refine ⟨202023144064208314340617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 269364192085611085787489 202023144064208314340617)
                    ·
                      refine ⟨151517358048156235755463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 202023144064208314340617 151517358048156235755463)
                      ·
                        rfl

theorem cell23_295079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_295079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295079 prefixEnd_295079 := by exact prefixLift 295079
  have htrace : WordTrace (prefixWord ++ tailWord_295079) baseStart_295079 baseEnd_295079 := by
    simpa [prefixWord, tailWord_295079, baseEnd_295079] using wordTrace_append hprefix tailTrace_295079
  have hstable : (prefixWord ++ tailWord_295079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295079).length < 2 ^ (prefixWord ++ tailWord_295079).sum := by decide
  have hdescent : baseEnd_295079 < baseStart_295079 := by decide
  rcases family_descends (prefixWord ++ tailWord_295079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295084 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 10]
def baseStart_295084 : Nat := 118140960795 + 295084 * 2 ^ 59
def prefixEnd_295084 : Nat := 4983230072969 + 3 ^ 40 * 295084 * 2
def baseEnd_295084 : Nat := 151519925451428716192939

theorem tailTrace_295084 : CollatzResearch.WordTrace tailWord_295084 prefixEnd_295084 151519925451428716192939 := by
  unfold tailWord_295084
  simp only [CollatzResearch.WordTrace]
  refine ⟨5381298831484269590026153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7175065108645692786701537 5381298831484269590026153)
  ·
    refine ⟨4035974123613202192519615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5381298831484269590026153 4035974123613202192519615)
    ·
      refine ⟨6053961185419803288779423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4035974123613202192519615 6053961185419803288779423)
      ·
        refine ⟨9080941778129704933169135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6053961185419803288779423 9080941778129704933169135)
        ·
          refine ⟨13621412667194557399753703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9080941778129704933169135 13621412667194557399753703)
          ·
            refine ⟨20432119000791836099630555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13621412667194557399753703 20432119000791836099630555)
            ·
              refine ⟨30648178501187754149445833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20432119000791836099630555 30648178501187754149445833)
              ·
                refine ⟨22986133875890815612084375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30648178501187754149445833 22986133875890815612084375)
                ·
                  refine ⟨34479200813836223418126563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22986133875890815612084375 34479200813836223418126563)
                  ·
                    refine ⟨51718801220754335127189845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34479200813836223418126563 51718801220754335127189845)
                    ·
                      refine ⟨151519925451428716192939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 51718801220754335127189845 151519925451428716192939)
                      ·
                        rfl

theorem cell23_295084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_295084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295084 prefixEnd_295084 := by exact prefixLift 295084
  have htrace : WordTrace (prefixWord ++ tailWord_295084) baseStart_295084 baseEnd_295084 := by
    simpa [prefixWord, tailWord_295084, baseEnd_295084] using wordTrace_append hprefix tailTrace_295084
  have hstable : (prefixWord ++ tailWord_295084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295084).length < 2 ^ (prefixWord ++ tailWord_295084).sum := by decide
  have hdescent : baseEnd_295084 < baseStart_295084 := by decide
  rcases family_descends (prefixWord ++ tailWord_295084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295089 : List Nat := [1, 2, 2, 5, 3, 1, 2, 1, 2, 4]
def baseStart_295089 : Nat := 118140960795 + 295089 * 2 ^ 59
def prefixEnd_295089 : Nat := 4983230072969 + 3 ^ 40 * 295089 * 2
def baseEnd_295089 : Nat := 50507497618233732210139

theorem tailTrace_295089 : CollatzResearch.WordTrace tailWord_295089 prefixEnd_295089 50507497618233732210139 := by
  unfold tailWord_295089
  simp only [CollatzResearch.WordTrace]
  refine ⟨10762780027950425033984321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7175186685300283355989547 10762780027950425033984321)
  ·
    refine ⟨8072085020962818775488241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10762780027950425033984321 8072085020962818775488241)
    ·
      refine ⟨6054063765722114081616181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8072085020962818775488241 6054063765722114081616181)
      ·
        refine ⟨567568478036448195151517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6054063765722114081616181 567568478036448195151517)
        ·
          refine ⟨212838179263668073181819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 567568478036448195151517 212838179263668073181819)
          ·
            refine ⟨319257268895502109772729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212838179263668073181819 319257268895502109772729)
            ·
              refine ⟨239442951671626582329547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319257268895502109772729 239442951671626582329547)
              ·
                refine ⟨359164427507439873494321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239442951671626582329547 359164427507439873494321)
                ·
                  refine ⟨269373320630579905120741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359164427507439873494321 269373320630579905120741)
                  ·
                    refine ⟨50507497618233732210139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 269373320630579905120741 50507497618233732210139)
                    ·
                      rfl

theorem cell23_295089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 2, 4].length) (baseStart_295089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295089 prefixEnd_295089 := by exact prefixLift 295089
  have htrace : WordTrace (prefixWord ++ tailWord_295089) baseStart_295089 baseEnd_295089 := by
    simpa [prefixWord, tailWord_295089, baseEnd_295089] using wordTrace_append hprefix tailTrace_295089
  have hstable : (prefixWord ++ tailWord_295089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295089).length < 2 ^ (prefixWord ++ tailWord_295089).sum := by decide
  have hdescent : baseEnd_295089 < baseStart_295089 := by decide
  rcases family_descends (prefixWord ++ tailWord_295089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295095 : List Nat := [1, 1, 3, 1, 4, 3, 1, 3, 2, 1, 3]
def baseStart_295095 : Nat := 118140960795 + 295095 * 2 ^ 59
def prefixEnd_295095 : Nat := 4983230072969 + 3 ^ 40 * 295095 * 2
def baseEnd_295095 : Nat := 151525573738628173155389

theorem tailTrace_295095 : CollatzResearch.WordTrace tailWord_295095 prefixEnd_295095 151525573738628173155389 := by
  unfold tailWord_295095
  simp only [CollatzResearch.WordTrace]
  refine ⟨10762998865928688058702739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7175332577285792039135159 10762998865928688058702739)
  ·
    refine ⟨16144498298893032088054109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10762998865928688058702739 16144498298893032088054109)
    ·
      refine ⟨6054186862084887033020291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16144498298893032088054109 6054186862084887033020291)
      ·
        refine ⟨9081280293127330549530437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6054186862084887033020291 9081280293127330549530437)
        ·
          refine ⟨1702740054961374478036957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9081280293127330549530437 1702740054961374478036957)
          ·
            refine ⟨638527520610515429263859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1702740054961374478036957 638527520610515429263859)
            ·
              refine ⟨957791280915773143895789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638527520610515429263859 957791280915773143895789)
              ·
                refine ⟨359171730343414928960921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 957791280915773143895789 359171730343414928960921)
                ·
                  refine ⟨269378797757561196720691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359171730343414928960921 269378797757561196720691)
                  ·
                    refine ⟨404068196636341795081037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 269378797757561196720691 404068196636341795081037)
                    ·
                      refine ⟨151525573738628173155389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 404068196636341795081037 151525573738628173155389)
                      ·
                        rfl

theorem cell23_295095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 1, 3].length) (baseStart_295095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295095 prefixEnd_295095 := by exact prefixLift 295095
  have htrace : WordTrace (prefixWord ++ tailWord_295095) baseStart_295095 baseEnd_295095 := by
    simpa [prefixWord, tailWord_295095, baseEnd_295095] using wordTrace_append hprefix tailTrace_295095
  have hstable : (prefixWord ++ tailWord_295095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295095).length < 2 ^ (prefixWord ++ tailWord_295095).sum := by decide
  have hdescent : baseEnd_295095 < baseStart_295095 := by decide
  rcases family_descends (prefixWord ++ tailWord_295095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295121 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 2, 1, 5]
def baseStart_295121 : Nat := 118140960795 + 295121 * 2 ^ 59
def prefixEnd_295121 : Nat := 4983230072969 + 3 ^ 40 * 295121 * 2
def baseEnd_295121 : Nat := 151538924235645071430269

theorem tailTrace_295121 : CollatzResearch.WordTrace tailWord_295121 prefixEnd_295121 151538924235645071430269 := by
  unfold tailWord_295121
  simp only [CollatzResearch.WordTrace]
  refine ⟨10763947163834494499149217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7175964775889662999432811 10763947163834494499149217)
  ·
    refine ⟨8072960372875870874361913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10763947163834494499149217 8072960372875870874361913)
    ·
      refine ⟨6054720279656903155771435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8072960372875870874361913 6054720279656903155771435)
      ·
        refine ⟨9082080419485354733657153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6054720279656903155771435 9082080419485354733657153)
        ·
          refine ⟨6811560314614016050242865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9082080419485354733657153 6811560314614016050242865)
          ·
            refine ⟨5108670235960512037682149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6811560314614016050242865 5108670235960512037682149)
            ·
              refine ⟨957875669242596007065403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5108670235960512037682149 957875669242596007065403)
              ·
                refine ⟨1436813503863894010598105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957875669242596007065403 1436813503863894010598105)
                ·
                  refine ⟨1077610127897920507948579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1436813503863894010598105 1077610127897920507948579)
                  ·
                    refine ⟨1616415191846880761922869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1077610127897920507948579 1616415191846880761922869)
                    ·
                      refine ⟨151538924235645071430269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1616415191846880761922869 151538924235645071430269)
                      ·
                        rfl

theorem cell23_295121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_295121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295121 prefixEnd_295121 := by exact prefixLift 295121
  have htrace : WordTrace (prefixWord ++ tailWord_295121) baseStart_295121 baseEnd_295121 := by
    simpa [prefixWord, tailWord_295121, baseEnd_295121] using wordTrace_append hprefix tailTrace_295121
  have hstable : (prefixWord ++ tailWord_295121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295121).length < 2 ^ (prefixWord ++ tailWord_295121).sum := by decide
  have hdescent : baseEnd_295121 < baseStart_295121 := by decide
  rcases family_descends (prefixWord ++ tailWord_295121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295171 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 1, 7]
def baseStart_295171 : Nat := 118140960795 + 295171 * 2 ^ 59
def prefixEnd_295171 : Nat := 4983230072969 + 3 ^ 40 * 295171 * 2
def baseEnd_295171 : Nat := 50521532756123291935013

theorem tailTrace_295171 : CollatzResearch.WordTrace tailWord_295171 prefixEnd_295171 50521532756123291935013 := by
  unfold tailWord_295171
  simp only [CollatzResearch.WordTrace]
  refine ⟨10765770813653353038469367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7177180542435568692312911 10765770813653353038469367)
  ·
    refine ⟨16148656220480029557704051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10765770813653353038469367 16148656220480029557704051)
    ·
      refine ⟨24222984330720044336556077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16148656220480029557704051 24222984330720044336556077)
      ·
        refine ⟨9083619124020016626208529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24222984330720044336556077 9083619124020016626208529)
        ·
          refine ⟨6812714343015012469656397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9083619124020016626208529 6812714343015012469656397)
          ·
            refine ⟨2554767878630629676121149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6812714343015012469656397 2554767878630629676121149)
            ·
              refine ⟨958037954486486128545431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2554767878630629676121149 958037954486486128545431)
              ·
                refine ⟨1437056931729729192818147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 958037954486486128545431 1437056931729729192818147)
                ·
                  refine ⟨2155585397594593789227221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437056931729729192818147 2155585397594593789227221)
                  ·
                    refine ⟨50521532756123291935013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2155585397594593789227221 50521532756123291935013)
                    ·
                      rfl

theorem cell23_295171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 7].length) (baseStart_295171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295171 prefixEnd_295171 := by exact prefixLift 295171
  have htrace : WordTrace (prefixWord ++ tailWord_295171) baseStart_295171 baseEnd_295171 := by
    simpa [prefixWord, tailWord_295171, baseEnd_295171] using wordTrace_append hprefix tailTrace_295171
  have hstable : (prefixWord ++ tailWord_295171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295171).length < 2 ^ (prefixWord ++ tailWord_295171).sum := by decide
  have hdescent : baseEnd_295171 < baseStart_295171 := by decide
  rcases family_descends (prefixWord ++ tailWord_295171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295228 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 1, 4, 3]
def baseStart_295228 : Nat := 118140960795 + 295228 * 2 ^ 59
def prefixEnd_295228 : Nat := 4983230072969 + 3 ^ 40 * 295228 * 2
def baseEnd_295228 : Nat := 151593866665676152792277

theorem tailTrace_295228 : CollatzResearch.WordTrace tailWord_295228 prefixEnd_295228 151593866665676152792277 := by
  unfold tailWord_295228
  simp only [CollatzResearch.WordTrace]
  refine ⟨5383924887223425886647169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7178566516297901182196225 5383924887223425886647169)
  ·
    refine ⟨4037943665417569414985377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5383924887223425886647169 4037943665417569414985377)
    ·
      refine ⟨3028457749063177061239033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4037943665417569414985377 3028457749063177061239033)
      ·
        refine ⟨2271343311797382795929275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3028457749063177061239033 2271343311797382795929275)
        ·
          refine ⟨3407014967696074193893913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2271343311797382795929275 3407014967696074193893913)
          ·
            refine ⟨2555261225772055645420435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3407014967696074193893913 2555261225772055645420435)
            ·
              refine ⟨3832891838658083468130653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2555261225772055645420435 3832891838658083468130653)
              ·
                refine ⟨1437334439496781300548995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3832891838658083468130653 1437334439496781300548995)
                ·
                  refine ⟨2156001659245171950823493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437334439496781300548995 2156001659245171950823493)
                  ·
                    refine ⟨404250311108469740779405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2156001659245171950823493 404250311108469740779405)
                    ·
                      refine ⟨151593866665676152792277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 404250311108469740779405 151593866665676152792277)
                      ·
                        rfl

theorem cell23_295228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_295228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295228 prefixEnd_295228 := by exact prefixLift 295228
  have htrace : WordTrace (prefixWord ++ tailWord_295228) baseStart_295228 baseEnd_295228 := by
    simpa [prefixWord, tailWord_295228, baseEnd_295228] using wordTrace_append hprefix tailTrace_295228
  have hstable : (prefixWord ++ tailWord_295228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295228).length < 2 ^ (prefixWord ++ tailWord_295228).sum := by decide
  have hdescent : baseEnd_295228 < baseStart_295228 := by decide
  rcases family_descends (prefixWord ++ tailWord_295228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295231 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 10]
def baseStart_295231 : Nat := 118140960795 + 295231 * 2 ^ 59
def prefixEnd_295231 : Nat := 4983230072969 + 3 ^ 40 * 295231 * 2
def baseEnd_295231 : Nat := 16843934123071071228307

theorem tailTrace_295231 : CollatzResearch.WordTrace tailWord_295231 prefixEnd_295231 16843934123071071228307 := by
  unfold tailWord_295231
  simp only [CollatzResearch.WordTrace]
  refine ⟨10767959193435983285653547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7178639462290655523769031 10767959193435983285653547)
  ·
    refine ⟨16151938790153974928480321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10767959193435983285653547 16151938790153974928480321)
    ·
      refine ⟨12113954092615481196360241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16151938790153974928480321 12113954092615481196360241)
      ·
        refine ⟨9085465569461610897270181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12113954092615481196360241 9085465569461610897270181)
        ·
          refine ⟨1703524794274052043238159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9085465569461610897270181 1703524794274052043238159)
          ·
            refine ⟨2555287191411078064857239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1703524794274052043238159 2555287191411078064857239)
            ·
              refine ⟨3832930787116617097285859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2555287191411078064857239 3832930787116617097285859)
              ·
                refine ⟨5749396180674925645928789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3832930787116617097285859 5749396180674925645928789)
                ·
                  refine ⟨16843934123071071228307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 5749396180674925645928789 16843934123071071228307)
                  ·
                    rfl

theorem cell23_295231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 10].length) (baseStart_295231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295231 prefixEnd_295231 := by exact prefixLift 295231
  have htrace : WordTrace (prefixWord ++ tailWord_295231) baseStart_295231 baseEnd_295231 := by
    simpa [prefixWord, tailWord_295231, baseEnd_295231] using wordTrace_append hprefix tailTrace_295231
  have hstable : (prefixWord ++ tailWord_295231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295231).length < 2 ^ (prefixWord ++ tailWord_295231).sum := by decide
  have hdescent : baseEnd_295231 < baseStart_295231 := by decide
  rcases family_descends (prefixWord ++ tailWord_295231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295251 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 6]
def baseStart_295251 : Nat := 118140960795 + 295251 * 2 ^ 59
def prefixEnd_295251 : Nat := 4983230072969 + 3 ^ 40 * 295251 * 2
def baseEnd_295251 : Nat := 151605676720729562804671

theorem tailTrace_295251 : CollatzResearch.WordTrace tailWord_295251 prefixEnd_295251 151605676720729562804671 := by
  unfold tailWord_295251
  simp only [CollatzResearch.WordTrace]
  refine ⟨10768688653363526701381607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7179125768909017800921071 10768688653363526701381607)
  ·
    refine ⟨16153032980045290052072411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10768688653363526701381607 16153032980045290052072411)
    ·
      refine ⟨24229549470067935078108617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16153032980045290052072411 24229549470067935078108617)
      ·
        refine ⟨18172162102550951308581463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24229549470067935078108617 18172162102550951308581463)
        ·
          refine ⟨27258243153826426962872195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18172162102550951308581463 27258243153826426962872195)
          ·
            refine ⟨40887364730739640444308293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27258243153826426962872195 40887364730739640444308293)
            ·
              refine ⟨7666380887013682583307805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40887364730739640444308293 7666380887013682583307805)
              ·
                refine ⟨2874892832630130968740427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7666380887013682583307805 2874892832630130968740427)
                ·
                  refine ⟨4312339248945196453110641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2874892832630130968740427 4312339248945196453110641)
                  ·
                    refine ⟨3234254436708897339832981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4312339248945196453110641 3234254436708897339832981)
                    ·
                      refine ⟨151605676720729562804671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3234254436708897339832981 151605676720729562804671)
                      ·
                        rfl

theorem cell23_295251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_295251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295251 prefixEnd_295251 := by exact prefixLift 295251
  have htrace : WordTrace (prefixWord ++ tailWord_295251) baseStart_295251 baseEnd_295251 := by
    simpa [prefixWord, tailWord_295251, baseEnd_295251] using wordTrace_append hprefix tailTrace_295251
  have hstable : (prefixWord ++ tailWord_295251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295251).length < 2 ^ (prefixWord ++ tailWord_295251).sum := by decide
  have hdescent : baseEnd_295251 < baseStart_295251 := by decide
  rcases family_descends (prefixWord ++ tailWord_295251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295252 : List Nat := [2, 4, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_295252 : Nat := 118140960795 + 295252 * 2 ^ 59
def prefixEnd_295252 : Nat := 4983230072969 + 3 ^ 40 * 295252 * 2
def baseEnd_295252 : Nat := 50535396733794686297389

theorem tailTrace_295252 : CollatzResearch.WordTrace tailWord_295252 prefixEnd_295252 50535396733794686297389 := by
  unfold tailWord_295252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5384362563179951936084005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7179150084239935914778673 5384362563179951936084005)
  ·
    refine ⟨1009567980596240988015751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5384362563179951936084005 1009567980596240988015751)
    ·
      refine ⟨1514351970894361482023627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1009567980596240988015751 1514351970894361482023627)
      ·
        refine ⟨2271527956341542223035441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1514351970894361482023627 2271527956341542223035441)
        ·
          refine ⟨1703645967256156667276581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2271527956341542223035441 1703645967256156667276581)
          ·
            refine ⟨319433618860529375114359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1703645967256156667276581 319433618860529375114359)
            ·
              refine ⟨479150428290794062671539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319433618860529375114359 479150428290794062671539)
              ·
                refine ⟨718725642436191094007309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479150428290794062671539 718725642436191094007309)
                ·
                  refine ⟨269522115913571660252741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718725642436191094007309 269522115913571660252741)
                  ·
                    refine ⟨50535396733794686297389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 269522115913571660252741 50535396733794686297389)
                    ·
                      rfl

theorem cell23_295252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_295252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295252 prefixEnd_295252 := by exact prefixLift 295252
  have htrace : WordTrace (prefixWord ++ tailWord_295252) baseStart_295252 baseEnd_295252 := by
    simpa [prefixWord, tailWord_295252, baseEnd_295252] using wordTrace_append hprefix tailTrace_295252
  have hstable : (prefixWord ++ tailWord_295252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295252).length < 2 ^ (prefixWord ++ tailWord_295252).sum := by decide
  have hdescent : baseEnd_295252 < baseStart_295252 := by decide
  rcases family_descends (prefixWord ++ tailWord_295252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295332 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 5, 2, 2]
def baseStart_295332 : Nat := 118140960795 + 295332 * 2 ^ 59
def prefixEnd_295332 : Nat := 4983230072969 + 3 ^ 40 * 295332 * 2
def baseEnd_295332 : Nat := 151647268653743745891799

theorem tailTrace_295332 : CollatzResearch.WordTrace tailWord_295332 prefixEnd_295332 151647268653743745891799 := by
  unfold tailWord_295332
  simp only [CollatzResearch.WordTrace]
  refine ⟨5385821483035038767540125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7181095310713385023386833 5385821483035038767540125)
  ·
    refine ⟨2019683056138139537827547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5385821483035038767540125 2019683056138139537827547)
    ·
      refine ⟨3029524584207209306741321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2019683056138139537827547 3029524584207209306741321)
      ·
        refine ⟨2272143438155406980055991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3029524584207209306741321 2272143438155406980055991)
        ·
          refine ⟨3408215157233110470083987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2272143438155406980055991 3408215157233110470083987)
          ·
            refine ⟨5112322735849665705125981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3408215157233110470083987 5112322735849665705125981)
            ·
              refine ⟨1917121025943624639422243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5112322735849665705125981 1917121025943624639422243)
              ·
                refine ⟨2875681538915436959133365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1917121025943624639422243 2875681538915436959133365)
                ·
                  refine ⟨269595144273322214918753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2875681538915436959133365 269595144273322214918753)
                  ·
                    refine ⟨202196358204991661189065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 269595144273322214918753 202196358204991661189065)
                    ·
                      refine ⟨151647268653743745891799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 202196358204991661189065 151647268653743745891799)
                      ·
                        rfl

theorem cell23_295332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_295332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295332 prefixEnd_295332 := by exact prefixLift 295332
  have htrace : WordTrace (prefixWord ++ tailWord_295332) baseStart_295332 baseEnd_295332 := by
    simpa [prefixWord, tailWord_295332, baseEnd_295332] using wordTrace_append hprefix tailTrace_295332
  have hstable : (prefixWord ++ tailWord_295332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295332).length < 2 ^ (prefixWord ++ tailWord_295332).sum := by decide
  have hdescent : baseEnd_295332 < baseStart_295332 := by decide
  rcases family_descends (prefixWord ++ tailWord_295332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295336 : List Nat := [2, 1, 6, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_295336 : Nat := 118140960795 + 295336 * 2 ^ 59
def prefixEnd_295336 : Nat := 4983230072969 + 3 ^ 40 * 295336 * 2
def baseEnd_295336 : Nat := 151649322576361730241781

theorem tailTrace_295336 : CollatzResearch.WordTrace tailWord_295336 prefixEnd_295336 151649322576361730241781 := by
  unfold tailWord_295336
  simp only [CollatzResearch.WordTrace]
  refine ⟨5385894429027793109112931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7181192572037057478817241 5385894429027793109112931)
  ·
    refine ⟨8078841643541689663669397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5385894429027793109112931 8078841643541689663669397)
    ·
      refine ⟨378695702041016702984503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8078841643541689663669397 378695702041016702984503)
      ·
        refine ⟨568043553061525054476755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378695702041016702984503 568043553061525054476755)
        ·
          refine ⟨852065329592287581715133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568043553061525054476755 852065329592287581715133)
          ·
            refine ⟨319524498597107843143175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 852065329592287581715133 319524498597107843143175)
            ·
              refine ⟨479286747895661764714763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319524498597107843143175 479286747895661764714763)
              ·
                refine ⟨718930121843492647072145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479286747895661764714763 718930121843492647072145)
                ·
                  refine ⟨539197591382619485304109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 718930121843492647072145 539197591382619485304109)
                  ·
                    refine ⟨202199096768482306989041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 539197591382619485304109 202199096768482306989041)
                    ·
                      refine ⟨151649322576361730241781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 202199096768482306989041 151649322576361730241781)
                      ·
                        rfl

theorem cell23_295336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_295336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295336 prefixEnd_295336 := by exact prefixLift 295336
  have htrace : WordTrace (prefixWord ++ tailWord_295336) baseStart_295336 baseEnd_295336 := by
    simpa [prefixWord, tailWord_295336, baseEnd_295336] using wordTrace_append hprefix tailTrace_295336
  have hstable : (prefixWord ++ tailWord_295336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295336).length < 2 ^ (prefixWord ++ tailWord_295336).sum := by decide
  have hdescent : baseEnd_295336 < baseStart_295336 := by decide
  rcases family_descends (prefixWord ++ tailWord_295336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295345 : List Nat := [1, 2, 2, 4, 1, 2, 2, 2, 1, 2, 4]
def baseStart_295345 : Nat := 118140960795 + 295345 * 2 ^ 59
def prefixEnd_295345 : Nat := 4983230072969 + 3 ^ 40 * 295345 * 2
def baseEnd_295345 : Nat := 151653943902252195029239

theorem tailTrace_295345 : CollatzResearch.WordTrace tailWord_295345 prefixEnd_295345 151653943902252195029239 := by
  unfold tailWord_295345
  simp only [CollatzResearch.WordTrace]
  refine ⟨10772117115022980755303489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7181411410015320503535659 10772117115022980755303489)
  ·
    refine ⟨8079087836267235566477617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10772117115022980755303489 8079087836267235566477617)
    ·
      refine ⟨6059315877200426674858213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8079087836267235566477617 6059315877200426674858213)
      ·
        refine ⟨1136121726975080001535915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6059315877200426674858213 1136121726975080001535915)
        ·
          refine ⟨1704182590462620002303873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1136121726975080001535915 1704182590462620002303873)
          ·
            refine ⟨1278136942846965001727905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1704182590462620002303873 1278136942846965001727905)
            ·
              refine ⟨958602707135223751295929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1278136942846965001727905 958602707135223751295929)
              ·
                refine ⟨718952030351417813471947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 958602707135223751295929 718952030351417813471947)
                ·
                  refine ⟨1078428045527126720207921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 718952030351417813471947 1078428045527126720207921)
                  ·
                    refine ⟨808821034145345040155941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1078428045527126720207921 808821034145345040155941)
                    ·
                      refine ⟨151653943902252195029239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 808821034145345040155941 151653943902252195029239)
                      ·
                        rfl

theorem cell23_295345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_295345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295345 prefixEnd_295345 := by exact prefixLift 295345
  have htrace : WordTrace (prefixWord ++ tailWord_295345) baseStart_295345 baseEnd_295345 := by
    simpa [prefixWord, tailWord_295345, baseEnd_295345] using wordTrace_append hprefix tailTrace_295345
  have hstable : (prefixWord ++ tailWord_295345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295345).length < 2 ^ (prefixWord ++ tailWord_295345).sum := by decide
  have hdescent : baseEnd_295345 < baseStart_295345 := by decide
  rcases family_descends (prefixWord ++ tailWord_295345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295418 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6]
def baseStart_295418 : Nat := 118140960795 + 295418 * 2 ^ 59
def prefixEnd_295418 : Nat := 4983230072969 + 3 ^ 40 * 295418 * 2
def baseEnd_295418 : Nat := 151691427990030409416403

theorem tailTrace_295418 : CollatzResearch.WordTrace tailWord_295418 prefixEnd_295418 151691427990030409416403 := by
  unfold tailWord_295418
  simp only [CollatzResearch.WordTrace]
  refine ⟨2693694910939628555677727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7183186429172342815140605 2693694910939628555677727)
  ·
    refine ⟨4040542366409442833516591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2693694910939628555677727 4040542366409442833516591)
    ·
      refine ⟨6060813549614164250274887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4040542366409442833516591 6060813549614164250274887)
      ·
        refine ⟨9091220324421246375412331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6060813549614164250274887 9091220324421246375412331)
        ·
          refine ⟨13636830486631869563118497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9091220324421246375412331 13636830486631869563118497)
          ·
            refine ⟨10227622864973902172338873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13636830486631869563118497 10227622864973902172338873)
            ·
              refine ⟨7670717148730426629254155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10227622864973902172338873 7670717148730426629254155)
              ·
                refine ⟨11506075723095639943881233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7670717148730426629254155 11506075723095639943881233)
                ·
                  refine ⟨8629556792321729957910925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11506075723095639943881233 8629556792321729957910925)
                  ·
                    refine ⟨3236083797120648734216597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8629556792321729957910925 3236083797120648734216597)
                    ·
                      refine ⟨151691427990030409416403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3236083797120648734216597 151691427990030409416403)
                      ·
                        rfl

theorem cell23_295418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_295418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295418 prefixEnd_295418 := by exact prefixLift 295418
  have htrace : WordTrace (prefixWord ++ tailWord_295418) baseStart_295418 baseEnd_295418 := by
    simpa [prefixWord, tailWord_295418, baseEnd_295418] using wordTrace_append hprefix tailTrace_295418
  have hstable : (prefixWord ++ tailWord_295418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295418).length < 2 ^ (prefixWord ++ tailWord_295418).sum := by decide
  have hdescent : baseEnd_295418 < baseStart_295418 := by decide
  rcases family_descends (prefixWord ++ tailWord_295418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295455 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 3]
def baseStart_295455 : Nat := 118140960795 + 295455 * 2 ^ 59
def prefixEnd_295455 : Nat := 4983230072969 + 3 ^ 40 * 295455 * 2
def baseEnd_295455 : Nat := 151710426774246764653733

theorem tailTrace_295455 : CollatzResearch.WordTrace tailWord_295455 prefixEnd_295455 151710426774246764653733 := by
  unfold tailWord_295455
  simp only [CollatzResearch.WordTrace]
  refine ⟨10776129144624469541807819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7184086096416313027871879 10776129144624469541807819)
  ·
    refine ⟨16164193716936704312711729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10776129144624469541807819 16164193716936704312711729)
    ·
      refine ⟨12123145287702528234533797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16164193716936704312711729 12123145287702528234533797)
      ·
        refine ⟨2273089741444224043975087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12123145287702528234533797 2273089741444224043975087)
        ·
          refine ⟨3409634612166336065962631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2273089741444224043975087 3409634612166336065962631)
          ·
            refine ⟨5114451918249504098943947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3409634612166336065962631 5114451918249504098943947)
            ·
              refine ⟨7671677877374256148415921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5114451918249504098943947 7671677877374256148415921)
              ·
                refine ⟨5753758408030692111311941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7671677877374256148415921 5753758408030692111311941)
                ·
                  refine ⟨1078829701505754770870989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5753758408030692111311941 1078829701505754770870989)
                  ·
                    refine ⟨404561138064658039076621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1078829701505754770870989 404561138064658039076621)
                    ·
                      refine ⟨151710426774246764653733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 404561138064658039076621 151710426774246764653733)
                      ·
                        rfl

theorem cell23_295455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_295455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295455 prefixEnd_295455 := by exact prefixLift 295455
  have htrace : WordTrace (prefixWord ++ tailWord_295455) baseStart_295455 baseEnd_295455 := by
    simpa [prefixWord, tailWord_295455, baseEnd_295455] using wordTrace_append hprefix tailTrace_295455
  have hstable : (prefixWord ++ tailWord_295455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295455).length < 2 ^ (prefixWord ++ tailWord_295455).sum := by decide
  have hdescent : baseEnd_295455 < baseStart_295455 := by decide
  rcases family_descends (prefixWord ++ tailWord_295455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295475 : List Nat := [1, 1, 1, 2, 4, 2, 1, 4, 2, 5]
def baseStart_295475 : Nat := 118140960795 + 295475 * 2 ^ 59
def prefixEnd_295475 : Nat := 4983230072969 + 3 ^ 40 * 295475 * 2
def baseEnd_295475 : Nat := 50573565462445562134547

theorem tailTrace_295475 : CollatzResearch.WordTrace tailWord_295475 prefixEnd_295475 50573565462445562134547 := by
  unfold tailWord_295475
  simp only [CollatzResearch.WordTrace]
  refine ⟨10776858604552012957535879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7184572403034675305023919 10776858604552012957535879)
  ·
    refine ⟨16165287906828019436303819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10776858604552012957535879 16165287906828019436303819)
    ·
      refine ⟨24247931860242029154455729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16165287906828019436303819 24247931860242029154455729)
      ·
        refine ⟨18185948895181521865841797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24247931860242029154455729 18185948895181521865841797)
        ·
          refine ⟨3409865417846535349845337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18185948895181521865841797 3409865417846535349845337)
          ·
            refine ⟨2557399063384901512384003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3409865417846535349845337 2557399063384901512384003)
            ·
              refine ⟨3836098595077352268576005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2557399063384901512384003 3836098595077352268576005)
              ·
                refine ⟨719268486577003550358001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3836098595077352268576005 719268486577003550358001)
                ·
                  refine ⟨539451364932752662768501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 719268486577003550358001 539451364932752662768501)
                  ·
                    refine ⟨50573565462445562134547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 539451364932752662768501 50573565462445562134547)
                    ·
                      rfl

theorem cell23_295475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 5].length) (baseStart_295475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295475 prefixEnd_295475 := by exact prefixLift 295475
  have htrace : WordTrace (prefixWord ++ tailWord_295475) baseStart_295475 baseEnd_295475 := by
    simpa [prefixWord, tailWord_295475, baseEnd_295475] using wordTrace_append hprefix tailTrace_295475
  have hstable : (prefixWord ++ tailWord_295475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295475).length < 2 ^ (prefixWord ++ tailWord_295475).sum := by decide
  have hdescent : baseEnd_295475 < baseStart_295475 := by decide
  rcases family_descends (prefixWord ++ tailWord_295475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295482 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2]
def baseStart_295482 : Nat := 118140960795 + 295482 * 2 ^ 59
def prefixEnd_295482 : Nat := 4983230072969 + 3 ^ 40 * 295482 * 2
def baseEnd_295482 : Nat := 151724290751918159016109

theorem tailTrace_295482 : CollatzResearch.WordTrace tailWord_295482 prefixEnd_295482 151724290751918159016109 := by
  unfold tailWord_295482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2694278478881663288260175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7184742610351102102027133 2694278478881663288260175)
  ·
    refine ⟨4041417718322494932390263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2694278478881663288260175 4041417718322494932390263)
    ·
      refine ⟨6062126577483742398585395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4041417718322494932390263 6062126577483742398585395)
      ·
        refine ⟨9093189866225613597878093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6062126577483742398585395 9093189866225613597878093)
        ·
          refine ⟨3409946199834605099204285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9093189866225613597878093 3409946199834605099204285)
          ·
            refine ⟨1278729824937976912201607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3409946199834605099204285 1278729824937976912201607)
            ·
              refine ⟨1918094737406965368302411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1278729824937976912201607 1918094737406965368302411)
              ·
                refine ⟨2877142106110448052453617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1918094737406965368302411 2877142106110448052453617)
                ·
                  refine ⟨2157856579582836039340213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2877142106110448052453617 2157856579582836039340213)
                  ·
                    refine ⟨202299054335890878688145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2157856579582836039340213 202299054335890878688145)
                    ·
                      refine ⟨151724290751918159016109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 202299054335890878688145 151724290751918159016109)
                      ·
                        rfl

theorem cell23_295482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2].length) (baseStart_295482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295482 prefixEnd_295482 := by exact prefixLift 295482
  have htrace : WordTrace (prefixWord ++ tailWord_295482) baseStart_295482 baseEnd_295482 := by
    simpa [prefixWord, tailWord_295482, baseEnd_295482] using wordTrace_append hprefix tailTrace_295482
  have hstable : (prefixWord ++ tailWord_295482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295482).length < 2 ^ (prefixWord ++ tailWord_295482).sum := by decide
  have hdescent : baseEnd_295482 < baseStart_295482 := by decide
  rcases family_descends (prefixWord ++ tailWord_295482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295512 : List Nat := [2, 1, 2, 2, 1, 2, 5, 1, 2, 1, 4]
def baseStart_295512 : Nat := 118140960795 + 295512 * 2 ^ 59
def prefixEnd_295512 : Nat := 4983230072969 + 3 ^ 40 * 295512 * 2
def baseEnd_295512 : Nat := 151739695171553041640971

theorem tailTrace_295512 : CollatzResearch.WordTrace tailWord_295512 prefixEnd_295512 151739695171553041640971 := by
  unfold tailWord_295512
  simp only [CollatzResearch.WordTrace]
  refine ⟨5389104052708984138316395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7185472070278645517755193 5389104052708984138316395)
  ·
    refine ⟨8083656079063476207474593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5389104052708984138316395 8083656079063476207474593)
    ·
      refine ⟨6062742059297607155605945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8083656079063476207474593 6062742059297607155605945)
      ·
        refine ⟨4547056544473205366704459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6062742059297607155605945 4547056544473205366704459)
        ·
          refine ⟨6820584816709808050056689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4547056544473205366704459 6820584816709808050056689)
          ·
            refine ⟨5115438612532356037542517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6820584816709808050056689 5115438612532356037542517)
            ·
              refine ⟨479572369924908378519611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5115438612532356037542517 479572369924908378519611)
              ·
                refine ⟨719358554887362567779417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479572369924908378519611 719358554887362567779417)
                ·
                  refine ⟨539518916165521925834563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 719358554887362567779417 539518916165521925834563)
                  ·
                    refine ⟨809278374248282888751845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 539518916165521925834563 809278374248282888751845)
                    ·
                      refine ⟨151739695171553041640971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 809278374248282888751845 151739695171553041640971)
                      ·
                        rfl

theorem cell23_295512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_295512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295512 prefixEnd_295512 := by exact prefixLift 295512
  have htrace : WordTrace (prefixWord ++ tailWord_295512) baseStart_295512 baseEnd_295512 := by
    simpa [prefixWord, tailWord_295512, baseEnd_295512] using wordTrace_append hprefix tailTrace_295512
  have hstable : (prefixWord ++ tailWord_295512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295512).length < 2 ^ (prefixWord ++ tailWord_295512).sum := by decide
  have hdescent : baseEnd_295512 < baseStart_295512 := by decide
  rcases family_descends (prefixWord ++ tailWord_295512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295532 : List Nat := [2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 3]
def baseStart_295532 : Nat := 118140960795 + 295532 * 2 ^ 59
def prefixEnd_295532 : Nat := 4983230072969 + 3 ^ 40 * 295532 * 2
def baseEnd_295532 : Nat := 151749964784642963390879

theorem tailTrace_295532 : CollatzResearch.WordTrace tailWord_295532 prefixEnd_295532 151749964784642963390879 := by
  unfold tailWord_295532
  simp only [CollatzResearch.WordTrace]
  refine ⟨5389468782672755846180425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7185958376897007794907233 5389468782672755846180425)
  ·
    refine ⟨4042101587004566884635319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5389468782672755846180425 4042101587004566884635319)
    ·
      refine ⟨6063152380506850326952979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4042101587004566884635319 6063152380506850326952979)
      ·
        refine ⟨9094728570760275490429469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6063152380506850326952979 9094728570760275490429469)
        ·
          refine ⟨3410523214035103308911051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9094728570760275490429469 3410523214035103308911051)
          ·
            refine ⟨5115784821052654963366577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3410523214035103308911051 5115784821052654963366577)
            ·
              refine ⟨3836838615789491222524933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5115784821052654963366577 3836838615789491222524933)
              ·
                refine ⟨719407240460529604223425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3836838615789491222524933 719407240460529604223425)
                ·
                  refine ⟨539555430345397203167569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 719407240460529604223425 539555430345397203167569)
                  ·
                    refine ⟨404666572759047902375677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 539555430345397203167569 404666572759047902375677)
                    ·
                      refine ⟨151749964784642963390879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 404666572759047902375677 151749964784642963390879)
                      ·
                        rfl

theorem cell23_295532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_295532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295532 prefixEnd_295532 := by exact prefixLift 295532
  have htrace : WordTrace (prefixWord ++ tailWord_295532) baseStart_295532 baseEnd_295532 := by
    simpa [prefixWord, tailWord_295532, baseEnd_295532] using wordTrace_append hprefix tailTrace_295532
  have hstable : (prefixWord ++ tailWord_295532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295532).length < 2 ^ (prefixWord ++ tailWord_295532).sum := by decide
  have hdescent : baseEnd_295532 < baseStart_295532 := by decide
  rcases family_descends (prefixWord ++ tailWord_295532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295602 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_295602 : Nat := 118140960795 + 295602 * 2 ^ 59
def prefixEnd_295602 : Nat := 4983230072969 + 3 ^ 40 * 295602 * 2
def baseEnd_295602 : Nat := 151785908430457689515557

theorem tailTrace_295602 : CollatzResearch.WordTrace tailWord_295602 prefixEnd_295602 151785908430457689515557 := by
  unfold tailWord_295602
  simp only [CollatzResearch.WordTrace]
  refine ⟨2695372668772978411852265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7187660450061275764939373 2695372668772978411852265)
  ·
    refine ⟨2021529501579733808889199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2695372668772978411852265 2021529501579733808889199)
    ·
      refine ⟨3032294252369600713333799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2021529501579733808889199 3032294252369600713333799)
      ·
        refine ⟨4548441378554401070000699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3032294252369600713333799 4548441378554401070000699)
        ·
          refine ⟨6822662067831601605001049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4548441378554401070000699 6822662067831601605001049)
          ·
            refine ⟨5116996550873701203750787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6822662067831601605001049 5116996550873701203750787)
            ·
              refine ⟨7675494826310551805626181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5116996550873701203750787 7675494826310551805626181)
              ·
                refine ⟨1439155279933228463554909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7675494826310551805626181 1439155279933228463554909)
                ·
                  refine ⟨539683229974960673833091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1439155279933228463554909 539683229974960673833091)
                  ·
                    refine ⟨809524844962441010749637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 539683229974960673833091 809524844962441010749637)
                    ·
                      refine ⟨151785908430457689515557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 809524844962441010749637 151785908430457689515557)
                      ·
                        rfl

theorem cell23_295602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_295602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295602 prefixEnd_295602 := by exact prefixLift 295602
  have htrace : WordTrace (prefixWord ++ tailWord_295602) baseStart_295602 baseEnd_295602 := by
    simpa [prefixWord, tailWord_295602, baseEnd_295602] using wordTrace_append hprefix tailTrace_295602
  have hstable : (prefixWord ++ tailWord_295602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295602).length < 2 ^ (prefixWord ++ tailWord_295602).sum := by decide
  have hdescent : baseEnd_295602 < baseStart_295602 := by decide
  rcases family_descends (prefixWord ++ tailWord_295602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295612 : List Nat := [2, 2, 2, 3, 1, 1, 2, 3, 1, 6]
def baseStart_295612 : Nat := 118140960795 + 295612 * 2 ^ 59
def prefixEnd_295612 : Nat := 4983230072969 + 3 ^ 40 * 295612 * 2
def baseEnd_295612 : Nat := 50597014412334216796837

theorem tailTrace_295612 : CollatzResearch.WordTrace tailWord_295612 prefixEnd_295612 50597014412334216796837 := by
  unfold tailWord_295612
  simp only [CollatzResearch.WordTrace]
  refine ⟨5390927702527842677636545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7187903603370456903515393 5390927702527842677636545)
  ·
    refine ⟨4043195776895882008227409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5390927702527842677636545 4043195776895882008227409)
    ·
      refine ⟨3032396832671911506170557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4043195776895882008227409 3032396832671911506170557)
      ·
        refine ⟨1137148812251966814813959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3032396832671911506170557 1137148812251966814813959)
        ·
          refine ⟨1705723218377950222220939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1137148812251966814813959 1705723218377950222220939)
          ·
            refine ⟨2558584827566925333331409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705723218377950222220939 2558584827566925333331409)
            ·
              refine ⟨1918938620675193999998557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2558584827566925333331409 1918938620675193999998557)
              ·
                refine ⟨719601982753197749999459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1918938620675193999998557 719601982753197749999459)
                ·
                  refine ⟨1079402974129796624999189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 719601982753197749999459 1079402974129796624999189)
                  ·
                    refine ⟨50597014412334216796837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1079402974129796624999189 50597014412334216796837)
                    ·
                      rfl

theorem cell23_295612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_295612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295612 prefixEnd_295612 := by exact prefixLift 295612
  have htrace : WordTrace (prefixWord ++ tailWord_295612) baseStart_295612 baseEnd_295612 := by
    simpa [prefixWord, tailWord_295612, baseEnd_295612] using wordTrace_append hprefix tailTrace_295612
  have hstable : (prefixWord ++ tailWord_295612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295612).length < 2 ^ (prefixWord ++ tailWord_295612).sum := by decide
  have hdescent : baseEnd_295612 < baseStart_295612 := by decide
  rcases family_descends (prefixWord ++ tailWord_295612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295639 : List Nat := [1, 1, 3, 2, 1, 6, 1, 1, 1, 1, 5]
def baseStart_295639 : Nat := 118140960795 + 295639 * 2 ^ 59
def prefixEnd_295639 : Nat := 4983230072969 + 3 ^ 40 * 295639 * 2
def baseEnd_295639 : Nat := 151804907214674044752887

theorem tailTrace_295639 : CollatzResearch.WordTrace tailWord_295639 prefixEnd_295639 151804907214674044752887 := by
  unfold tailWord_295639
  simp only [CollatzResearch.WordTrace]
  refine ⟨10782840175957868966505971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7188560117305245977670647 10782840175957868966505971)
  ·
    refine ⟨16174260263936803449758957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10782840175957868966505971 16174260263936803449758957)
    ·
      refine ⟨6065347598976301293659609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16174260263936803449758957 6065347598976301293659609)
      ·
        refine ⟨4549010699232225970244707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6065347598976301293659609 4549010699232225970244707)
        ·
          refine ⟨6823516048848338955367061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4549010699232225970244707 6823516048848338955367061)
          ·
            refine ⟨319852314789765888532831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6823516048848338955367061 319852314789765888532831)
            ·
              refine ⟨479778472184648832799247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319852314789765888532831 479778472184648832799247)
              ·
                refine ⟨719667708276973249198871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479778472184648832799247 719667708276973249198871)
                ·
                  refine ⟨1079501562415459873798307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 719667708276973249198871 1079501562415459873798307)
                  ·
                    refine ⟨1619252343623189810697461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1079501562415459873798307 1619252343623189810697461)
                    ·
                      refine ⟨151804907214674044752887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1619252343623189810697461 151804907214674044752887)
                      ·
                        rfl

theorem cell23_295639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_295639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295639 prefixEnd_295639 := by exact prefixLift 295639
  have htrace : WordTrace (prefixWord ++ tailWord_295639) baseStart_295639 baseEnd_295639 := by
    simpa [prefixWord, tailWord_295639, baseEnd_295639] using wordTrace_append hprefix tailTrace_295639
  have hstable : (prefixWord ++ tailWord_295639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295639).length < 2 ^ (prefixWord ++ tailWord_295639).sum := by decide
  have hdescent : baseEnd_295639 < baseStart_295639 := by decide
  rcases family_descends (prefixWord ++ tailWord_295639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295749 : List Nat := [1, 3, 1, 1, 1, 2, 2, 7, 5]
def baseStart_295749 : Nat := 118140960795 + 295749 * 2 ^ 59
def prefixEnd_295749 : Nat := 4983230072969 + 3 ^ 40 * 295749 * 2
def baseEnd_295749 : Nat := 16873487787407623819709

theorem tailTrace_295749 : CollatzResearch.WordTrace tailWord_295749 prefixEnd_295749 16873487787407623819709 := by
  unfold tailWord_295749
  simp only [CollatzResearch.WordTrace]
  refine ⟨10786852205559357753010301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7191234803706238502006867 10786852205559357753010301)
  ·
    refine ⟨4045069577084759157378863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10786852205559357753010301 4045069577084759157378863)
    ·
      refine ⟨6067604365627138736068295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4045069577084759157378863 6067604365627138736068295)
      ·
        refine ⟨9101406548440708104102443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6067604365627138736068295 9101406548440708104102443)
        ·
          refine ⟨13652109822661062156153665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9101406548440708104102443 13652109822661062156153665)
          ·
            refine ⟨10239082366995796617115249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13652109822661062156153665 10239082366995796617115249)
            ·
              refine ⟨7679311775246847462836437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10239082366995796617115249 7679311775246847462836437)
              ·
                refine ⟨179983869732347987410229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7679311775246847462836437 179983869732347987410229)
                ·
                  refine ⟨16873487787407623819709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 179983869732347987410229 16873487787407623819709)
                  ·
                    rfl

theorem cell23_295749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 5].length) (baseStart_295749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295749 prefixEnd_295749 := by exact prefixLift 295749
  have htrace : WordTrace (prefixWord ++ tailWord_295749) baseStart_295749 baseEnd_295749 := by
    simpa [prefixWord, tailWord_295749, baseEnd_295749] using wordTrace_append hprefix tailTrace_295749
  have hstable : (prefixWord ++ tailWord_295749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295749).length < 2 ^ (prefixWord ++ tailWord_295749).sum := by decide
  have hdescent : baseEnd_295749 < baseStart_295749 := by decide
  rcases family_descends (prefixWord ++ tailWord_295749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295792 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 2, 8]
def baseStart_295792 : Nat := 118140960795 + 295792 * 2 ^ 59
def prefixEnd_295792 : Nat := 4983230072969 + 3 ^ 40 * 295792 * 2
def baseEnd_295792 : Nat := 50627823251603982046561

theorem tailTrace_295792 : CollatzResearch.WordTrace tailWord_295792 prefixEnd_295792 50627823251603982046561 := by
  unfold tailWord_295792
  simp only [CollatzResearch.WordTrace]
  refine ⟨5394210272201788048412815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7192280362935717397883753 5394210272201788048412815)
  ·
    refine ⟨8091315408302682072619223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5394210272201788048412815 8091315408302682072619223)
    ·
      refine ⟨12136973112454023108928835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8091315408302682072619223 12136973112454023108928835)
      ·
        refine ⟨18205459668681034663393253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12136973112454023108928835 18205459668681034663393253)
        ·
          refine ⟨3413523687877693999386235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18205459668681034663393253 3413523687877693999386235)
          ·
            refine ⟨5120285531816540999079353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3413523687877693999386235 5120285531816540999079353)
            ·
              refine ⟨3840214148862405749309515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5120285531816540999079353 3840214148862405749309515)
              ·
                refine ⟨5760321223293608623964273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3840214148862405749309515 5760321223293608623964273)
                ·
                  refine ⟨4320240917470206467973205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5760321223293608623964273 4320240917470206467973205)
                  ·
                    refine ⟨50627823251603982046561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4320240917470206467973205 50627823251603982046561)
                    ·
                      rfl

theorem cell23_295792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 8].length) (baseStart_295792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295792 prefixEnd_295792 := by exact prefixLift 295792
  have htrace : WordTrace (prefixWord ++ tailWord_295792) baseStart_295792 baseEnd_295792 := by
    simpa [prefixWord, tailWord_295792, baseEnd_295792] using wordTrace_append hprefix tailTrace_295792
  have hstable : (prefixWord ++ tailWord_295792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295792).length < 2 ^ (prefixWord ++ tailWord_295792).sum := by decide
  have hdescent : baseEnd_295792 < baseStart_295792 := by decide
  rcases family_descends (prefixWord ++ tailWord_295792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295816 : List Nat := [2, 1, 3, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_295816 : Nat := 118140960795 + 295816 * 2 ^ 59
def prefixEnd_295816 : Nat := 4983230072969 + 3 ^ 40 * 295816 * 2
def baseEnd_295816 : Nat := 151895793290519852239573

theorem tailTrace_295816 : CollatzResearch.WordTrace tailWord_295816 prefixEnd_295816 151895793290519852239573 := by
  unfold tailWord_295816
  simp only [CollatzResearch.WordTrace]
  refine ⟨5394647948158314097849651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7192863930877752130466201 5394647948158314097849651)
  ·
    refine ⟨8091971922237471146774477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5394647948158314097849651 8091971922237471146774477)
    ·
      refine ⟨3034489470839051680040429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8091971922237471146774477 3034489470839051680040429)
      ·
        refine ⟨1137933551564644380015161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3034489470839051680040429 1137933551564644380015161)
        ·
          refine ⟨853450163673483285011371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1137933551564644380015161 853450163673483285011371)
          ·
            refine ⟨1280175245510224927517057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853450163673483285011371 1280175245510224927517057)
            ·
              refine ⟨960131434132668695637793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1280175245510224927517057 960131434132668695637793)
              ·
                refine ⟨720098575599501521728345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 960131434132668695637793 720098575599501521728345)
                ·
                  refine ⟨540073931699626141296259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 720098575599501521728345 540073931699626141296259)
                  ·
                    refine ⟨810110897549439211944389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 540073931699626141296259 810110897549439211944389)
                    ·
                      refine ⟨151895793290519852239573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 810110897549439211944389 151895793290519852239573)
                      ·
                        rfl

theorem cell23_295816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_295816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295816 prefixEnd_295816 := by exact prefixLift 295816
  have htrace : WordTrace (prefixWord ++ tailWord_295816) baseStart_295816 baseEnd_295816 := by
    simpa [prefixWord, tailWord_295816, baseEnd_295816] using wordTrace_append hprefix tailTrace_295816
  have hstable : (prefixWord ++ tailWord_295816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295816).length < 2 ^ (prefixWord ++ tailWord_295816).sum := by decide
  have hdescent : baseEnd_295816 < baseStart_295816 := by decide
  rcases family_descends (prefixWord ++ tailWord_295816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
