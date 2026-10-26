import V185TrunkScan23Chunk1203

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7132527 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 9]
def baseStart_7132527 : Nat := 118140960795 + 7132527 * 2 ^ 59
def prefixEnd_7132527 : Nat := 4983230072969 + 3 ^ 40 * 7132527 * 2
def baseEnd_7132527 : Nat := 406934959130124521001179

theorem tailTrace_7132527 : CollatzResearch.WordTrace tailWord_7132527 prefixEnd_7132527 406934959130124521001179 := by
  unfold tailWord_7132527
  simp only [CollatzResearch.WordTrace]
  refine ⟨260144631431080292475739835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173429754287386861650493223 260144631431080292475739835)
  ·
    refine ⟨390216947146620438713609753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260144631431080292475739835 390216947146620438713609753)
    ·
      refine ⟨292662710359965329035207315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390216947146620438713609753 292662710359965329035207315)
      ·
        refine ⟨438994065539947993552810973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292662710359965329035207315 438994065539947993552810973)
        ·
          refine ⟨164622774577480497582304115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 438994065539947993552810973 164622774577480497582304115)
          ·
            refine ⟨246934161866220746373456173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164622774577480497582304115 246934161866220746373456173)
            ·
              refine ⟨92600310699832779890046065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246934161866220746373456173 92600310699832779890046065)
              ·
                refine ⟨69450233024874584917534549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92600310699832779890046065 69450233024874584917534549)
                ·
                  refine ⟨406934959130124521001179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69450233024874584917534549 406934959130124521001179)
                  ·
                    rfl

theorem cell23_7132527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 9].length) (baseStart_7132527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132527 prefixEnd_7132527 := by exact prefixLift 7132527
  have htrace : WordTrace (prefixWord ++ tailWord_7132527) baseStart_7132527 baseEnd_7132527 := by
    simpa [prefixWord, tailWord_7132527, baseEnd_7132527] using wordTrace_append hprefix tailTrace_7132527
  have hstable : (prefixWord ++ tailWord_7132527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132527).length < 2 ^ (prefixWord ++ tailWord_7132527).sum := by decide
  have hdescent : baseEnd_7132527 < baseStart_7132527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132555 : List Nat := [1, 1, 1, 1, 4, 3, 5, 1, 2, 2, 2]
def baseStart_7132555 : Nat := 118140960795 + 7132555 * 2 ^ 59
def prefixEnd_7132555 : Nat := 4983230072969 + 3 ^ 40 * 7132555 * 2
def baseEnd_7132555 : Nat := 3662429009629446579460483

theorem tailTrace_7132555 : CollatzResearch.WordTrace tailWord_7132555 prefixEnd_7132555 3662429009629446579460483 := by
  unfold tailWord_7132555
  simp only [CollatzResearch.WordTrace]
  refine ⟨260145652674978853257759119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173430435116652568838506079 260145652674978853257759119)
  ·
    refine ⟨390218479012468279886638679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260145652674978853257759119 390218479012468279886638679)
    ·
      refine ⟨585327718518702419829958019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390218479012468279886638679 585327718518702419829958019)
      ·
        refine ⟨877991577778053629744937029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585327718518702419829958019 877991577778053629744937029)
        ·
          refine ⟨164623420833385055577175693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 877991577778053629744937029 164623420833385055577175693)
          ·
            refine ⟨61733782812519395841440885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164623420833385055577175693 61733782812519395841440885)
            ·
              refine ⟨5787542138673693360135083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61733782812519395841440885 5787542138673693360135083)
              ·
                refine ⟨8681313208010540040202625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5787542138673693360135083 8681313208010540040202625)
                ·
                  refine ⟨6510984906007905030151969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8681313208010540040202625 6510984906007905030151969)
                  ·
                    refine ⟨4883238679505928772613977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6510984906007905030151969 4883238679505928772613977)
                    ·
                      refine ⟨3662429009629446579460483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4883238679505928772613977 3662429009629446579460483)
                      ·
                        rfl

theorem cell23_7132555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 2, 2, 2].length) (baseStart_7132555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132555 prefixEnd_7132555 := by exact prefixLift 7132555
  have htrace : WordTrace (prefixWord ++ tailWord_7132555) baseStart_7132555 baseEnd_7132555 := by
    simpa [prefixWord, tailWord_7132555, baseEnd_7132555] using wordTrace_append hprefix tailTrace_7132555
  have hstable : (prefixWord ++ tailWord_7132555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132555).length < 2 ^ (prefixWord ++ tailWord_7132555).sum := by decide
  have hdescent : baseEnd_7132555 < baseStart_7132555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132578 : List Nat := [3, 3, 1, 2, 1, 2, 3, 3, 5]
def baseStart_7132578 : Nat := 118140960795 + 7132578 * 2 ^ 59
def prefixEnd_7132578 : Nat := 4983230072969 + 3 ^ 40 * 7132578 * 2
def baseEnd_7132578 : Nat := 406937868853833332163653

theorem tailTrace_7132578 : CollatzResearch.WordTrace tailWord_7132578 prefixEnd_7132578 406937868853833332163653 := by
  unfold tailWord_7132578
  simp only [CollatzResearch.WordTrace]
  refine ⟨65036622888473882046461597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173430994369263685457230925 65036622888473882046461597)
  ·
    refine ⟨24388733583177705767423099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65036622888473882046461597 24388733583177705767423099)
    ·
      refine ⟨36583100374766558651134649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24388733583177705767423099 36583100374766558651134649)
      ·
        refine ⟨27437325281074918988350987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36583100374766558651134649 27437325281074918988350987)
        ·
          refine ⟨41155987921612378482526481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27437325281074918988350987 41155987921612378482526481)
          ·
            refine ⟨30866990941209283861894861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41155987921612378482526481 30866990941209283861894861)
            ·
              refine ⟨11575121602953481448210573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30866990941209283861894861 11575121602953481448210573)
              ·
                refine ⟨4340670601107555543078965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11575121602953481448210573 4340670601107555543078965)
                ·
                  refine ⟨406937868853833332163653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4340670601107555543078965 406937868853833332163653)
                  ·
                    rfl

theorem cell23_7132578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_7132578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132578 prefixEnd_7132578 := by exact prefixLift 7132578
  have htrace : WordTrace (prefixWord ++ tailWord_7132578) baseStart_7132578 baseEnd_7132578 := by
    simpa [prefixWord, tailWord_7132578, baseEnd_7132578] using wordTrace_append hprefix tailTrace_7132578
  have hstable : (prefixWord ++ tailWord_7132578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132578).length < 2 ^ (prefixWord ++ tailWord_7132578).sum := by decide
  have hdescent : baseEnd_7132578 < baseStart_7132578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132594 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_7132594 : Nat := 118140960795 + 7132594 * 2 ^ 59
def prefixEnd_7132594 : Nat := 4983230072969 + 3 ^ 40 * 7132594 * 2
def baseEnd_7132594 : Nat := 3662449035374971926872803

theorem tailTrace_7132594 : CollatzResearch.WordTrace tailWord_7132594 prefixEnd_7132594 3662449035374971926872803 := by
  unfold tailWord_7132594
  simp only [CollatzResearch.WordTrace]
  refine ⟨65036768780459390729607209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173431383414558375278952557 65036768780459390729607209)
  ·
    refine ⟨48777576585344543047205407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65036768780459390729607209 48777576585344543047205407)
    ·
      refine ⟨73166364878016814570808111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48777576585344543047205407 73166364878016814570808111)
      ·
        refine ⟨109749547317025221856212167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73166364878016814570808111 109749547317025221856212167)
        ·
          refine ⟨164624320975537832784318251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109749547317025221856212167 164624320975537832784318251)
          ·
            refine ⟨246936481463306749176477377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164624320975537832784318251 246936481463306749176477377)
            ·
              refine ⟨185202361097480061882358033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246936481463306749176477377 185202361097480061882358033)
              ·
                refine ⟨138901770823110046411768525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185202361097480061882358033 138901770823110046411768525)
                ·
                  refine ⟨52088164058666267404413197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138901770823110046411768525 52088164058666267404413197)
                  ·
                    refine ⟨19533061521999850276654949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52088164058666267404413197 19533061521999850276654949)
                    ·
                      refine ⟨3662449035374971926872803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19533061521999850276654949 3662449035374971926872803)
                      ·
                        rfl

theorem cell23_7132594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_7132594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132594 prefixEnd_7132594 := by exact prefixLift 7132594
  have htrace : WordTrace (prefixWord ++ tailWord_7132594) baseStart_7132594 baseEnd_7132594 := by
    simpa [prefixWord, tailWord_7132594, baseEnd_7132594] using wordTrace_append hprefix tailTrace_7132594
  have hstable : (prefixWord ++ tailWord_7132594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132594).length < 2 ^ (prefixWord ++ tailWord_7132594).sum := by decide
  have hdescent : baseEnd_7132594 < baseStart_7132594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132601 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 1, 2, 5]
def baseStart_7132601 : Nat := 118140960795 + 7132601 * 2 ^ 59
def prefixEnd_7132601 : Nat := 4983230072969 + 3 ^ 40 * 7132601 * 2
def baseEnd_7132601 : Nat := 3662452629739553399485271

theorem tailTrace_7132601 : CollatzResearch.WordTrace tailWord_7132601 prefixEnd_7132601 3662452629739553399485271 := by
  unfold tailWord_7132601
  simp only [CollatzResearch.WordTrace]
  refine ⟨260147330432812203113933657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173431553621874802075955771 260147330432812203113933657)
  ·
    refine ⟨195110497824609152335450243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260147330432812203113933657 195110497824609152335450243)
    ·
      refine ⟨292665746736913728503175365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195110497824609152335450243 292665746736913728503175365)
      ·
        refine ⟨54874827513171324094345381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292665746736913728503175365 54874827513171324094345381)
        ·
          refine ⟨10289030158719623267689759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54874827513171324094345381 10289030158719623267689759)
          ·
            refine ⟨15433545238079434901534639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10289030158719623267689759 15433545238079434901534639)
            ·
              refine ⟨23150317857119152352301959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15433545238079434901534639 23150317857119152352301959)
              ·
                refine ⟨34725476785678728528452939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23150317857119152352301959 34725476785678728528452939)
                ·
                  refine ⟨52088215178518092792679409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34725476785678728528452939 52088215178518092792679409)
                  ·
                    refine ⟨39066161383888569594509557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52088215178518092792679409 39066161383888569594509557)
                    ·
                      refine ⟨3662452629739553399485271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39066161383888569594509557 3662452629739553399485271)
                      ·
                        rfl

theorem cell23_7132601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_7132601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132601 prefixEnd_7132601 := by exact prefixLift 7132601
  have htrace : WordTrace (prefixWord ++ tailWord_7132601) baseStart_7132601 baseEnd_7132601 := by
    simpa [prefixWord, tailWord_7132601, baseEnd_7132601] using wordTrace_append hprefix tailTrace_7132601
  have hstable : (prefixWord ++ tailWord_7132601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132601).length < 2 ^ (prefixWord ++ tailWord_7132601).sum := by decide
  have hdescent : baseEnd_7132601 < baseStart_7132601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132611 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 2, 4, 2]
def baseStart_7132611 : Nat := 118140960795 + 7132611 * 2 ^ 59
def prefixEnd_7132611 : Nat := 4983230072969 + 3 ^ 40 * 7132611 * 2
def baseEnd_7132611 : Nat := 3662457764546098360360225

theorem tailTrace_7132611 : CollatzResearch.WordTrace tailWord_7132611 prefixEnd_7132611 3662457764546098360360225 := by
  unfold tailWord_7132611
  simp only [CollatzResearch.WordTrace]
  refine ⟨260147695162775974821797687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173431796775183983214531791 260147695162775974821797687)
  ·
    refine ⟨390221542744163962232696531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260147695162775974821797687 390221542744163962232696531)
    ·
      refine ⟨585332314116245943349044797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390221542744163962232696531 585332314116245943349044797)
      ·
        refine ⟨219499617793592228755891799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 585332314116245943349044797 219499617793592228755891799)
        ·
          refine ⟨329249426690388343133837699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219499617793592228755891799 329249426690388343133837699)
          ·
            refine ⟨493874140035582514700756549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329249426690388343133837699 493874140035582514700756549)
            ·
              refine ⟨92601401256671721506391853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 493874140035582514700756549 92601401256671721506391853)
              ·
                refine ⟨34725525471251895564896945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92601401256671721506391853 34725525471251895564896945)
                ·
                  refine ⟨26044144103438921673672709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34725525471251895564896945 26044144103438921673672709)
                  ·
                    refine ⟨4883277019394797813813633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26044144103438921673672709 4883277019394797813813633)
                    ·
                      refine ⟨3662457764546098360360225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4883277019394797813813633 3662457764546098360360225)
                      ·
                        rfl

theorem cell23_7132611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 4, 2].length) (baseStart_7132611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132611 prefixEnd_7132611 := by exact prefixLift 7132611
  have htrace : WordTrace (prefixWord ++ tailWord_7132611) baseStart_7132611 baseEnd_7132611 := by
    simpa [prefixWord, tailWord_7132611, baseEnd_7132611] using wordTrace_append hprefix tailTrace_7132611
  have hstable : (prefixWord ++ tailWord_7132611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132611).length < 2 ^ (prefixWord ++ tailWord_7132611).sum := by decide
  have hdescent : baseEnd_7132611 < baseStart_7132611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132655 : List Nat := [1, 1, 2, 1, 4, 1, 6, 2, 1, 4]
def baseStart_7132655 : Nat := 118140960795 + 7132655 * 2 ^ 59
def prefixEnd_7132655 : Nat := 4983230072969 + 3 ^ 40 * 7132655 * 2
def baseEnd_7132655 : Nat := 1220826785898298729403341

theorem tailTrace_7132655 : CollatzResearch.WordTrace tailWord_7132655 prefixEnd_7132655 1220826785898298729403341 := by
  unfold tailWord_7132655
  simp only [CollatzResearch.WordTrace]
  refine ⟨260149299974616570336399419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173432866649744380224266279 260149299974616570336399419)
  ·
    refine ⟨390223949961924855504599129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260149299974616570336399419 390223949961924855504599129)
    ·
      refine ⟨292667962471443641628449347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390223949961924855504599129 292667962471443641628449347)
      ·
        refine ⟨439001943707165462442674021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292667962471443641628449347 439001943707165462442674021)
        ·
          refine ⟨82312864445093524208001379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 439001943707165462442674021 82312864445093524208001379)
          ·
            refine ⟨123469296667640286312002069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82312864445093524208001379 123469296667640286312002069)
            ·
              refine ⟨5787623281295638420875097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123469296667640286312002069 5787623281295638420875097)
              ·
                refine ⟨4340717460971728815656323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5787623281295638420875097 4340717460971728815656323)
                ·
                  refine ⟨6511076191457593223484485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340717460971728815656323 6511076191457593223484485)
                  ·
                    refine ⟨1220826785898298729403341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6511076191457593223484485 1220826785898298729403341)
                    ·
                      rfl

theorem cell23_7132655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 1, 4].length) (baseStart_7132655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132655 prefixEnd_7132655 := by exact prefixLift 7132655
  have htrace : WordTrace (prefixWord ++ tailWord_7132655) baseStart_7132655 baseEnd_7132655 := by
    simpa [prefixWord, tailWord_7132655, baseEnd_7132655] using wordTrace_append hprefix tailTrace_7132655
  have hstable : (prefixWord ++ tailWord_7132655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132655).length < 2 ^ (prefixWord ++ tailWord_7132655).sum := by decide
  have hdescent : baseEnd_7132655 < baseStart_7132655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132681 : List Nat := [1, 2, 1, 1, 3, 1, 4, 4, 1, 5]
def baseStart_7132681 : Nat := 118140960795 + 7132681 * 2 ^ 59
def prefixEnd_7132681 : Nat := 4983230072969 + 3 ^ 40 * 7132681 * 2
def baseEnd_7132681 : Nat := 1220831236063971028828301

theorem tailTrace_7132681 : CollatzResearch.WordTrace tailWord_7132681 prefixEnd_7132681 1220831236063971028828301 := by
  unfold tailWord_7132681
  simp only [CollatzResearch.WordTrace]
  refine ⟨260150248272522376776845897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173433498848348251184563931 260150248272522376776845897)
  ·
    refine ⟨195112686204391782582634423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260150248272522376776845897 195112686204391782582634423)
    ·
      refine ⟨292669029306587673873951635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195112686204391782582634423 292669029306587673873951635)
      ·
        refine ⟨439003543959881510810927453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292669029306587673873951635 439003543959881510810927453)
        ·
          refine ⟨164626328984955566554097795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 439003543959881510810927453 164626328984955566554097795)
          ·
            refine ⟨246939493477433349831146693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164626328984955566554097795 246939493477433349831146693)
            ·
              refine ⟨46301155027018753093340005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246939493477433349831146693 46301155027018753093340005)
              ·
                refine ⟨8681466567566016205001251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46301155027018753093340005 8681466567566016205001251)
                ·
                  refine ⟨13022199851349024307501877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8681466567566016205001251 13022199851349024307501877)
                  ·
                    refine ⟨1220831236063971028828301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13022199851349024307501877 1220831236063971028828301)
                    ·
                      rfl

theorem cell23_7132681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 5].length) (baseStart_7132681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132681 prefixEnd_7132681 := by exact prefixLift 7132681
  have htrace : WordTrace (prefixWord ++ tailWord_7132681) baseStart_7132681 baseEnd_7132681 := by
    simpa [prefixWord, tailWord_7132681, baseEnd_7132681] using wordTrace_append hprefix tailTrace_7132681
  have hstable : (prefixWord ++ tailWord_7132681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132681).length < 2 ^ (prefixWord ++ tailWord_7132681).sum := by decide
  have hdescent : baseEnd_7132681 < baseStart_7132681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132702 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 8]
def baseStart_7132702 : Nat := 118140960795 + 7132702 * 2 ^ 59
def prefixEnd_7132702 : Nat := 4983230072969 + 3 ^ 40 * 7132702 * 2
def baseEnd_7132702 : Nat := 406944943476184167146923

theorem tailTrace_7132702 : CollatzResearch.WordTrace tailWord_7132702 prefixEnd_7132702 406944943476184167146923 := by
  unfold tailWord_7132702
  simp only [CollatzResearch.WordTrace]
  refine ⟨32518876775680787170420045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173434009470297531575573573 32518876775680787170420045)
  ·
    refine ⟨12194578790880295188907517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32518876775680787170420045 12194578790880295188907517)
    ·
      refine ⟨4572967046580110695840319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12194578790880295188907517 4572967046580110695840319)
      ·
        refine ⟨6859450569870166043760479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4572967046580110695840319 6859450569870166043760479)
        ·
          refine ⟨10289175854805249065640719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6859450569870166043760479 10289175854805249065640719)
          ·
            refine ⟨15433763782207873598461079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10289175854805249065640719 15433763782207873598461079)
            ·
              refine ⟨23150645673311810397691619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15433763782207873598461079 23150645673311810397691619)
              ·
                refine ⟨34725968509967715596537429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23150645673311810397691619 34725968509967715596537429)
                ·
                  refine ⟨406944943476184167146923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34725968509967715596537429 406944943476184167146923)
                  ·
                    rfl

theorem cell23_7132702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_7132702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132702 prefixEnd_7132702 := by exact prefixLift 7132702
  have htrace : WordTrace (prefixWord ++ tailWord_7132702) baseStart_7132702 baseEnd_7132702 := by
    simpa [prefixWord, tailWord_7132702, baseEnd_7132702] using wordTrace_append hprefix tailTrace_7132702
  have hstable : (prefixWord ++ tailWord_7132702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132702).length < 2 ^ (prefixWord ++ tailWord_7132702).sum := by decide
  have hdescent : baseEnd_7132702 < baseStart_7132702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132712 : List Nat := [2, 1, 5, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_7132712 : Nat := 118140960795 + 7132712 * 2 ^ 59
def prefixEnd_7132712 : Nat := 4983230072969 + 3 ^ 40 * 7132712 * 2
def baseEnd_7132712 : Nat := 3662509626092202465197261

theorem tailTrace_7132712 : CollatzResearch.WordTrace tailWord_7132712 prefixEnd_7132712 3662509626092202465197261 := by
  unfold tailWord_7132712
  simp only [CollatzResearch.WordTrace]
  refine ⟨130075689467705034535612195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173434252623606712714149593 130075689467705034535612195)
  ·
    refine ⟨195113534201557551803418293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130075689467705034535612195 195113534201557551803418293)
    ·
      refine ⟨18291893831396020481570465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195113534201557551803418293 18291893831396020481570465)
      ·
        refine ⟨13718920373547015361177849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18291893831396020481570465 13718920373547015361177849)
        ·
          refine ⟨10289190280160261520883387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13718920373547015361177849 10289190280160261520883387)
          ·
            refine ⟨15433785420240392281325081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10289190280160261520883387 15433785420240392281325081)
            ·
              refine ⟨11575339065180294210993811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15433785420240392281325081 11575339065180294210993811)
              ·
                refine ⟨17363008597770441316490717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11575339065180294210993811 17363008597770441316490717)
                ·
                  refine ⟨6511128224163915493684019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17363008597770441316490717 6511128224163915493684019)
                  ·
                    refine ⟨9766692336245873240526029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6511128224163915493684019 9766692336245873240526029)
                    ·
                      refine ⟨3662509626092202465197261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9766692336245873240526029 3662509626092202465197261)
                      ·
                        rfl

theorem cell23_7132712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_7132712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132712 prefixEnd_7132712 := by exact prefixLift 7132712
  have htrace : WordTrace (prefixWord ++ tailWord_7132712) baseStart_7132712 baseEnd_7132712 := by
    simpa [prefixWord, tailWord_7132712, baseEnd_7132712] using wordTrace_append hprefix tailTrace_7132712
  have hstable : (prefixWord ++ tailWord_7132712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132712).length < 2 ^ (prefixWord ++ tailWord_7132712).sum := by decide
  have hdescent : baseEnd_7132712 < baseStart_7132712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132728 : List Nat := [2, 1, 2, 1, 4, 4, 1, 1, 1, 6]
def baseStart_7132728 : Nat := 118140960795 + 7132728 * 2 ^ 59
def prefixEnd_7132728 : Nat := 4983230072969 + 3 ^ 40 * 7132728 * 2
def baseEnd_7132728 : Nat := 1220839280594224800865729

theorem tailTrace_7132728 : CollatzResearch.WordTrace tailWord_7132728 prefixEnd_7132728 1220839280594224800865729 := by
  unfold tailWord_7132728
  simp only [CollatzResearch.WordTrace]
  refine ⟨130075981251676051901903419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173434641668901402535871225 130075981251676051901903419)
  ·
    refine ⟨195113971877514077852855129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130075981251676051901903419 195113971877514077852855129)
    ·
      refine ⟨146335478908135558389641347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195113971877514077852855129 146335478908135558389641347)
      ·
        refine ⟨219503218362203337584462021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146335478908135558389641347 219503218362203337584462021)
        ·
          refine ⟨41156853442913125797086629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219503218362203337584462021 41156853442913125797086629)
          ·
            refine ⟨7716910020546211086953743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41156853442913125797086629 7716910020546211086953743)
            ·
              refine ⟨11575365030819316630430615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7716910020546211086953743 11575365030819316630430615)
              ·
                refine ⟨17363047546228974945645923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11575365030819316630430615 17363047546228974945645923)
                ·
                  refine ⟨26044571319343462418468885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17363047546228974945645923 26044571319343462418468885)
                  ·
                    refine ⟨1220839280594224800865729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26044571319343462418468885 1220839280594224800865729)
                    ·
                      rfl

theorem cell23_7132728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_7132728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132728 prefixEnd_7132728 := by exact prefixLift 7132728
  have htrace : WordTrace (prefixWord ++ tailWord_7132728) baseStart_7132728 baseEnd_7132728 := by
    simpa [prefixWord, tailWord_7132728, baseEnd_7132728] using wordTrace_append hprefix tailTrace_7132728
  have hstable : (prefixWord ++ tailWord_7132728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132728).length < 2 ^ (prefixWord ++ tailWord_7132728).sum := by decide
  have hdescent : baseEnd_7132728 < baseStart_7132728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132735 : List Nat := [1, 1, 2, 2, 3, 3, 2, 2, 3, 2, 2]
def baseStart_7132735 : Nat := 118140960795 + 7132735 * 2 ^ 59
def prefixEnd_7132735 : Nat := 4983230072969 + 3 ^ 40 * 7132735 * 2
def baseEnd_7132735 : Nat := 3662521436147255875209655

theorem tailTrace_7132735 : CollatzResearch.WordTrace tailWord_7132735 prefixEnd_7132735 3662521436147255875209655 := by
  unfold tailWord_7132735
  simp only [CollatzResearch.WordTrace]
  refine ⟨260152217814326743999311659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173434811876217829332874439 260152217814326743999311659)
  ·
    refine ⟨390228326721490115998967489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260152217814326743999311659 390228326721490115998967489)
    ·
      refine ⟨292671245041117586999225617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390228326721490115998967489 292671245041117586999225617)
      ·
        refine ⟨219503433780838190249419213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292671245041117586999225617 219503433780838190249419213)
        ·
          refine ⟨82313787667814321343532205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219503433780838190249419213 82313787667814321343532205)
          ·
            refine ⟨30867670375430370503824577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82313787667814321343532205 30867670375430370503824577)
            ·
              refine ⟨23150752781572777877868433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30867670375430370503824577 23150752781572777877868433)
              ·
                refine ⟨17363064586179583408401325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23150752781572777877868433 17363064586179583408401325)
                ·
                  refine ⟨6511149219817343778150497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17363064586179583408401325 6511149219817343778150497)
                  ·
                    refine ⟨4883361914863007833612873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6511149219817343778150497 4883361914863007833612873)
                    ·
                      refine ⟨3662521436147255875209655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4883361914863007833612873 3662521436147255875209655)
                      ·
                        rfl

theorem cell23_7132735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 2, 2].length) (baseStart_7132735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132735 prefixEnd_7132735 := by exact prefixLift 7132735
  have htrace : WordTrace (prefixWord ++ tailWord_7132735) baseStart_7132735 baseEnd_7132735 := by
    simpa [prefixWord, tailWord_7132735, baseEnd_7132735] using wordTrace_append hprefix tailTrace_7132735
  have hstable : (prefixWord ++ tailWord_7132735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132735).length < 2 ^ (prefixWord ++ tailWord_7132735).sum := by decide
  have hdescent : baseEnd_7132735 < baseStart_7132735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132751 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 3]
def baseStart_7132751 : Nat := 118140960795 + 7132751 * 2 ^ 59
def prefixEnd_7132751 : Nat := 4983230072969 + 3 ^ 40 * 7132751 * 2
def baseEnd_7132751 : Nat := 3662529651837727812609581

theorem tailTrace_7132751 : CollatzResearch.WordTrace tailWord_7132751 prefixEnd_7132751 3662529651837727812609581 := by
  unfold tailWord_7132751
  simp only [CollatzResearch.WordTrace]
  refine ⟨260152801382268778731894107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173435200921512519154596071 260152801382268778731894107)
  ·
    refine ⟨390229202073403168097841161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260152801382268778731894107 390229202073403168097841161)
    ·
      refine ⟨292671901555052376073380871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390229202073403168097841161 292671901555052376073380871)
      ·
        refine ⟨439007852332578564110071307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292671901555052376073380871 439007852332578564110071307)
        ·
          refine ⟨658511778498867846165106961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439007852332578564110071307 658511778498867846165106961)
          ·
            refine ⟨493883833874150884623830221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658511778498867846165106961 493883833874150884623830221)
            ·
              refine ⟨185206437702806581733936333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 493883833874150884623830221 185206437702806581733936333)
              ·
                refine ⟨69452414138552468150226125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185206437702806581733936333 69452414138552468150226125)
                ·
                  refine ⟨26044655301957175556334797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69452414138552468150226125 26044655301957175556334797)
                  ·
                    refine ⟨9766745738233940833625549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26044655301957175556334797 9766745738233940833625549)
                    ·
                      refine ⟨3662529651837727812609581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9766745738233940833625549 3662529651837727812609581)
                      ·
                        rfl

theorem cell23_7132751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 3].length) (baseStart_7132751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132751 prefixEnd_7132751 := by exact prefixLift 7132751
  have htrace : WordTrace (prefixWord ++ tailWord_7132751) baseStart_7132751 baseEnd_7132751 := by
    simpa [prefixWord, tailWord_7132751, baseEnd_7132751] using wordTrace_append hprefix tailTrace_7132751
  have hstable : (prefixWord ++ tailWord_7132751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132751).length < 2 ^ (prefixWord ++ tailWord_7132751).sum := by decide
  have hdescent : baseEnd_7132751 < baseStart_7132751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132769 : List Nat := [1, 2, 3, 1, 1, 3, 5, 2, 1, 2, 2]
def baseStart_7132769 : Nat := 118140960795 + 7132769 * 2 ^ 59
def prefixEnd_7132769 : Nat := 4983230072969 + 3 ^ 40 * 7132769 * 2
def baseEnd_7132769 : Nat := 3662538894489508742184499

theorem tailTrace_7132769 : CollatzResearch.WordTrace tailWord_7132769 prefixEnd_7132769 3662538894489508742184499 := by
  unfold tailWord_7132769
  simp only [CollatzResearch.WordTrace]
  refine ⟨260153457896203567806049361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173435638597469045204032907 260153457896203567806049361)
  ·
    refine ⟨195115093422152675854537021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260153457896203567806049361 195115093422152675854537021)
    ·
      refine ⟨73168160033307253445451383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195115093422152675854537021 73168160033307253445451383)
      ·
        refine ⟨109752240049960880168177075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73168160033307253445451383 109752240049960880168177075)
        ·
          refine ⟨164628360074941320252265613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109752240049960880168177075 164628360074941320252265613)
          ·
            refine ⟨61735635028102995094599605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164628360074941320252265613 61735635028102995094599605)
            ·
              refine ⟨5787715783884655790118713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61735635028102995094599605 5787715783884655790118713)
              ·
                refine ⟨4340786837913491842589035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5787715783884655790118713 4340786837913491842589035)
                ·
                  refine ⟨6511180256870237763883553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340786837913491842589035 6511180256870237763883553)
                  ·
                    refine ⟨4883385192652678322912665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6511180256870237763883553 4883385192652678322912665)
                    ·
                      refine ⟨3662538894489508742184499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4883385192652678322912665 3662538894489508742184499)
                      ·
                        rfl

theorem cell23_7132769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_7132769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132769 prefixEnd_7132769 := by exact prefixLift 7132769
  have htrace : WordTrace (prefixWord ++ tailWord_7132769) baseStart_7132769 baseEnd_7132769 := by
    simpa [prefixWord, tailWord_7132769, baseEnd_7132769] using wordTrace_append hprefix tailTrace_7132769
  have hstable : (prefixWord ++ tailWord_7132769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132769).length < 2 ^ (prefixWord ++ tailWord_7132769).sum := by decide
  have hdescent : baseEnd_7132769 < baseStart_7132769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132811 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 5]
def baseStart_7132811 : Nat := 118140960795 + 7132811 * 2 ^ 59
def prefixEnd_7132811 : Nat := 4983230072969 + 3 ^ 40 * 7132811 * 2
def baseEnd_7132811 : Nat := 3662560460676997577859305

theorem tailTrace_7132811 : CollatzResearch.WordTrace tailWord_7132811 prefixEnd_7132811 3662560460676997577859305 := by
  unfold tailWord_7132811
  simp only [CollatzResearch.WordTrace]
  refine ⟨260154989762051408979078287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173436659841367605986052191 260154989762051408979078287)
  ·
    refine ⟨390232484643077113468617431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260154989762051408979078287 390232484643077113468617431)
    ·
      refine ⟨585348726964615670202926147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390232484643077113468617431 585348726964615670202926147)
      ·
        refine ⟨878023090446923505304389221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585348726964615670202926147 878023090446923505304389221)
        ·
          refine ⟨164629329458798157244572979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 878023090446923505304389221 164629329458798157244572979)
          ·
            refine ⟨246943994188197235866859469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164629329458798157244572979 246943994188197235866859469)
            ·
              refine ⟨92603997820573963450072301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246943994188197235866859469 92603997820573963450072301)
              ·
                refine ⟨34726499182715236293777113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92603997820573963450072301 34726499182715236293777113)
                ·
                  refine ⟨26044874387036427220332835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34726499182715236293777113 26044874387036427220332835)
                  ·
                    refine ⟨39067311580554640830499253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26044874387036427220332835 39067311580554640830499253)
                    ·
                      refine ⟨3662560460676997577859305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39067311580554640830499253 3662560460676997577859305)
                      ·
                        rfl

theorem cell23_7132811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 5].length) (baseStart_7132811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132811 prefixEnd_7132811 := by exact prefixLift 7132811
  have htrace : WordTrace (prefixWord ++ tailWord_7132811) baseStart_7132811 baseEnd_7132811 := by
    simpa [prefixWord, tailWord_7132811, baseEnd_7132811] using wordTrace_append hprefix tailTrace_7132811
  have hstable : (prefixWord ++ tailWord_7132811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132811).length < 2 ^ (prefixWord ++ tailWord_7132811).sum := by decide
  have hdescent : baseEnd_7132811 < baseStart_7132811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132812 : List Nat := [2, 2, 1, 2, 1, 1, 7, 1, 1, 3, 2]
def baseStart_7132812 : Nat := 118140960795 + 7132812 * 2 ^ 59
def prefixEnd_7132812 : Nat := 4983230072969 + 3 ^ 40 * 7132812 * 2
def baseEnd_7132812 : Nat := 3662560974157652073946801

theorem tailTrace_7132812 : CollatzResearch.WordTrace tailWord_7132812 prefixEnd_7132812 3662560974157652073946801 := by
  unfold tailWord_7132812
  simp only [CollatzResearch.WordTrace]
  refine ⟨130077513117523893074932345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173436684156698524099909793 130077513117523893074932345)
  ·
    refine ⟨97558134838142919806199259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130077513117523893074932345 97558134838142919806199259)
    ·
      refine ⟨146337202257214379709298889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97558134838142919806199259 146337202257214379709298889)
      ·
        refine ⟨109752901692910784781974167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146337202257214379709298889 109752901692910784781974167)
        ·
          refine ⟨164629352539366177172961251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109752901692910784781974167 164629352539366177172961251)
          ·
            refine ⟨246944028809049265759441877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164629352539366177172961251 246944028809049265759441877)
            ·
              refine ⟨5787750675212092166236919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 246944028809049265759441877 5787750675212092166236919)
              ·
                refine ⟨8681626012818138249355379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5787750675212092166236919 8681626012818138249355379)
                ·
                  refine ⟨13022439019227207374033069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8681626012818138249355379 13022439019227207374033069)
                  ·
                    refine ⟨4883414632210202765262401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13022439019227207374033069 4883414632210202765262401)
                    ·
                      refine ⟨3662560974157652073946801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4883414632210202765262401 3662560974157652073946801)
                      ·
                        rfl

theorem cell23_7132812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_7132812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132812 prefixEnd_7132812 := by exact prefixLift 7132812
  have htrace : WordTrace (prefixWord ++ tailWord_7132812) baseStart_7132812 baseEnd_7132812 := by
    simpa [prefixWord, tailWord_7132812, baseEnd_7132812] using wordTrace_append hprefix tailTrace_7132812
  have hstable : (prefixWord ++ tailWord_7132812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132812).length < 2 ^ (prefixWord ++ tailWord_7132812).sum := by decide
  have hdescent : baseEnd_7132812 < baseStart_7132812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132820 : List Nat := [2, 4, 2, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_7132820 : Nat := 118140960795 + 7132820 * 2 ^ 59
def prefixEnd_7132820 : Nat := 4983230072969 + 3 ^ 40 * 7132820 * 2
def baseEnd_7132820 : Nat := 3662565082002888042646765

theorem tailTrace_7132820 : CollatzResearch.WordTrace tailWord_7132820 prefixEnd_7132820 3662565082002888042646765 := by
  unfold tailWord_7132820
  simp only [CollatzResearch.WordTrace]
  refine ⟨130077659009509401758077957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173436878679345869010770609 130077659009509401758077957)
  ·
    refine ⟨24389561064283012829639617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130077659009509401758077957 24389561064283012829639617)
    ·
      refine ⟨18292170798212259622229713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24389561064283012829639617 18292170798212259622229713)
      ·
        refine ⟨13719128098659194716672285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18292170798212259622229713 13719128098659194716672285)
        ·
          refine ⟨5144673036997198018752107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13719128098659194716672285 5144673036997198018752107)
          ·
            refine ⟨7717009555495797028128161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5144673036997198018752107 7717009555495797028128161)
            ·
              refine ⟨5787757166621847771096121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7717009555495797028128161 5787757166621847771096121)
              ·
                refine ⟨4340817874966385828322091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5787757166621847771096121 4340817874966385828322091)
                ·
                  refine ⟨6511226812449578742483137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340817874966385828322091 6511226812449578742483137)
                  ·
                    refine ⟨4883420109337184056862353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6511226812449578742483137 4883420109337184056862353)
                    ·
                      refine ⟨3662565082002888042646765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4883420109337184056862353 3662565082002888042646765)
                      ·
                        rfl

theorem cell23_7132820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_7132820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132820 prefixEnd_7132820 := by exact prefixLift 7132820
  have htrace : WordTrace (prefixWord ++ tailWord_7132820) baseStart_7132820 baseEnd_7132820 := by
    simpa [prefixWord, tailWord_7132820, baseEnd_7132820] using wordTrace_append hprefix tailTrace_7132820
  have hstable : (prefixWord ++ tailWord_7132820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132820).length < 2 ^ (prefixWord ++ tailWord_7132820).sum := by decide
  have hdescent : baseEnd_7132820 < baseStart_7132820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132821 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_7132821 : Nat := 118140960795 + 7132821 * 2 ^ 59
def prefixEnd_7132821 : Nat := 4983230072969 + 3 ^ 40 * 7132821 * 2
def baseEnd_7132821 : Nat := 3662565595483542538734259

theorem tailTrace_7132821 : CollatzResearch.WordTrace tailWord_7132821 prefixEnd_7132821 3662565595483542538734259 := by
  unfold tailWord_7132821
  simp only [CollatzResearch.WordTrace]
  refine ⟨260155354492015180686942317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173436902994676787124628211 260155354492015180686942317)
  ·
    refine ⟨97558257934505692757603369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260155354492015180686942317 97558257934505692757603369)
    ·
      refine ⟨73168693450879269568202527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97558257934505692757603369 73168693450879269568202527)
      ·
        refine ⟨109753040176318904352303791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73168693450879269568202527 109753040176318904352303791)
        ·
          refine ⟨164629560264478356528455687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109753040176318904352303791 164629560264478356528455687)
          ·
            refine ⟨246944340396717534792683531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164629560264478356528455687 246944340396717534792683531)
            ·
              refine ⟨370416510595076302189025297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246944340396717534792683531 370416510595076302189025297)
              ·
                refine ⟨277812382946307226641768973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370416510595076302189025297 277812382946307226641768973)
                ·
                  refine ⟨104179643604865209990663365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277812382946307226641768973 104179643604865209990663365)
                  ·
                    refine ⟨19533683175912226873249381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104179643604865209990663365 19533683175912226873249381)
                    ·
                      refine ⟨3662565595483542538734259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19533683175912226873249381 3662565595483542538734259)
                      ·
                        rfl

theorem cell23_7132821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_7132821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132821 prefixEnd_7132821 := by exact prefixLift 7132821
  have htrace : WordTrace (prefixWord ++ tailWord_7132821) baseStart_7132821 baseEnd_7132821 := by
    simpa [prefixWord, tailWord_7132821, baseEnd_7132821] using wordTrace_append hprefix tailTrace_7132821
  have hstable : (prefixWord ++ tailWord_7132821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132821).length < 2 ^ (prefixWord ++ tailWord_7132821).sum := by decide
  have hdescent : baseEnd_7132821 < baseStart_7132821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132876 : List Nat := [2, 2, 1, 5, 2, 2, 1, 2, 2, 2, 2]
def baseStart_7132876 : Nat := 118140960795 + 7132876 * 2 ^ 59
def prefixEnd_7132876 : Nat := 4983230072969 + 3 ^ 40 * 7132876 * 2
def baseEnd_7132876 : Nat := 3662593836919539823546507

theorem tailTrace_7132876 : CollatzResearch.WordTrace tailWord_7132876 prefixEnd_7132876 3662593836919539823546507 := by
  unfold tailWord_7132876
  simp only [CollatzResearch.WordTrace]
  refine ⟨130078680253407962540097241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173438240337877283386796321 130078680253407962540097241)
  ·
    refine ⟨97559010190055971905072931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130078680253407962540097241 97559010190055971905072931)
    ·
      refine ⟨146338515285083957857609397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97559010190055971905072931 146338515285083957857609397)
      ·
        refine ⟨13719235807976621049150881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146338515285083957857609397 13719235807976621049150881)
        ·
          refine ⟨10289426855982465786863161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13719235807976621049150881 10289426855982465786863161)
          ·
            refine ⟨7717070141986849340147371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10289426855982465786863161 7717070141986849340147371)
            ·
              refine ⟨11575605212980274010221057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7717070141986849340147371 11575605212980274010221057)
              ·
                refine ⟨8681703909735205507665793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11575605212980274010221057 8681703909735205507665793)
                ·
                  refine ⟨6511277932301404130749345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8681703909735205507665793 6511277932301404130749345)
                  ·
                    refine ⟨4883458449226053098062009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6511277932301404130749345 4883458449226053098062009)
                    ·
                      refine ⟨3662593836919539823546507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4883458449226053098062009 3662593836919539823546507)
                      ·
                        rfl

theorem cell23_7132876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_7132876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132876 prefixEnd_7132876 := by exact prefixLift 7132876
  have htrace : WordTrace (prefixWord ++ tailWord_7132876) baseStart_7132876 baseEnd_7132876 := by
    simpa [prefixWord, tailWord_7132876, baseEnd_7132876] using wordTrace_append hprefix tailTrace_7132876
  have hstable : (prefixWord ++ tailWord_7132876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132876).length < 2 ^ (prefixWord ++ tailWord_7132876).sum := by decide
  have hdescent : baseEnd_7132876 < baseStart_7132876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132878 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 4, 5]
def baseStart_7132878 : Nat := 118140960795 + 7132878 * 2 ^ 59
def prefixEnd_7132878 : Nat := 4983230072969 + 3 ^ 40 * 7132878 * 2
def baseEnd_7132878 : Nat := 1220864954626949605240499

theorem tailTrace_7132878 : CollatzResearch.WordTrace tailWord_7132878 prefixEnd_7132878 1220864954626949605240499 := by
  unfold tailWord_7132878
  simp only [CollatzResearch.WordTrace]
  refine ⟨32519679181601084927720911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173438288968539119614511525 32519679181601084927720911)
  ·
    refine ⟨48779518772401627391581367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32519679181601084927720911 48779518772401627391581367)
    ·
      refine ⟨73169278158602441087372051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48779518772401627391581367 73169278158602441087372051)
      ·
        refine ⟨109753917237903661631058077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73169278158602441087372051 109753917237903661631058077)
        ·
          refine ⟨41157718964213873111646779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109753917237903661631058077 41157718964213873111646779)
          ·
            refine ⟨61736578446320809667470169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41157718964213873111646779 61736578446320809667470169)
            ·
              refine ⟨46302433834740607250602627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61736578446320809667470169 46302433834740607250602627)
              ·
                refine ⟨69453650752110910875903941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46302433834740607250602627 69453650752110910875903941)
                ·
                  refine ⟨13022559516020795789231989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69453650752110910875903941 13022559516020795789231989)
                  ·
                    refine ⟨1220864954626949605240499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13022559516020795789231989 1220864954626949605240499)
                    ·
                      rfl

theorem cell23_7132878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_7132878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132878 prefixEnd_7132878 := by exact prefixLift 7132878
  have htrace : WordTrace (prefixWord ++ tailWord_7132878) baseStart_7132878 baseEnd_7132878 := by
    simpa [prefixWord, tailWord_7132878, baseEnd_7132878] using wordTrace_append hprefix tailTrace_7132878
  have hstable : (prefixWord ++ tailWord_7132878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132878).length < 2 ^ (prefixWord ++ tailWord_7132878).sum := by decide
  have hdescent : baseEnd_7132878 < baseStart_7132878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132893 : List Nat := [1, 4, 3, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_7132893 : Nat := 118140960795 + 7132893 * 2 ^ 59
def prefixEnd_7132893 : Nat := 4983230072969 + 3 ^ 40 * 7132893 * 2
def baseEnd_7132893 : Nat := 3662602566090666257033929

theorem tailTrace_7132893 : CollatzResearch.WordTrace tailWord_7132893 prefixEnd_7132893 3662602566090666257033929 := by
  unfold tailWord_7132893
  simp only [CollatzResearch.WordTrace]
  refine ⟨260157980547754336983563333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173438653698502891322375555 260157980547754336983563333)
  ·
    refine ⟨48779621352703938184418125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260157980547754336983563333 48779621352703938184418125)
    ·
      refine ⟨18292358007263976819156797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48779621352703938184418125 18292358007263976819156797)
      ·
        refine ⟨6859634252723991307183799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18292358007263976819156797 6859634252723991307183799)
        ·
          refine ⟨10289451379085986960775699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6859634252723991307183799 10289451379085986960775699)
          ·
            refine ⟨15434177068628980441163549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10289451379085986960775699 15434177068628980441163549)
            ·
              refine ⟨5787816400735867665436331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15434177068628980441163549 5787816400735867665436331)
              ·
                refine ⟨8681724601103801498154497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5787816400735867665436331 8681724601103801498154497)
                ·
                  refine ⟨6511293450827851123615873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8681724601103801498154497 6511293450827851123615873)
                  ·
                    refine ⟨4883470088120888342711905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6511293450827851123615873 4883470088120888342711905)
                    ·
                      refine ⟨3662602566090666257033929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4883470088120888342711905 3662602566090666257033929)
                      ·
                        rfl

theorem cell23_7132893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_7132893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132893 prefixEnd_7132893 := by exact prefixLift 7132893
  have htrace : WordTrace (prefixWord ++ tailWord_7132893) baseStart_7132893 baseEnd_7132893 := by
    simpa [prefixWord, tailWord_7132893, baseEnd_7132893] using wordTrace_append hprefix tailTrace_7132893
  have hstable : (prefixWord ++ tailWord_7132893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132893).length < 2 ^ (prefixWord ++ tailWord_7132893).sum := by decide
  have hdescent : baseEnd_7132893 < baseStart_7132893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132916 : List Nat := [2, 6, 1, 1, 1, 3, 1, 3, 5]
def baseStart_7132916 : Nat := 118140960795 + 7132916 * 2 ^ 59
def prefixEnd_7132916 : Nat := 4983230072969 + 3 ^ 40 * 7132916 * 2
def baseEnd_7132916 : Nat := 406957152905079963005147

theorem tailTrace_7132916 : CollatzResearch.WordTrace tailWord_7132916 prefixEnd_7132916 406957152905079963005147 := by
  unfold tailWord_7132916
  simp only [CollatzResearch.WordTrace]
  refine ⟨130079409713335505955825301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173439212951114007941100401 130079409713335505955825301)
  ·
    refine ⟨6097472330312601841679311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 130079409713335505955825301 6097472330312601841679311)
    ·
      refine ⟨9146208495468902762518967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6097472330312601841679311 9146208495468902762518967)
      ·
        refine ⟨13719312743203354143778451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9146208495468902762518967 13719312743203354143778451)
        ·
          refine ⟨20578969114805031215667677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13719312743203354143778451 20578969114805031215667677)
          ·
            refine ⟨7717113418051886705875379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20578969114805031215667677 7717113418051886705875379)
            ·
              refine ⟨11575670127077830058813069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7717113418051886705875379 11575670127077830058813069)
              ·
                refine ⟨4340876297654186272054901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11575670127077830058813069 4340876297654186272054901)
                ·
                  refine ⟨406957152905079963005147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4340876297654186272054901 406957152905079963005147)
                  ·
                    rfl

theorem cell23_7132916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_7132916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132916 prefixEnd_7132916 := by exact prefixLift 7132916
  have htrace : WordTrace (prefixWord ++ tailWord_7132916) baseStart_7132916 baseEnd_7132916 := by
    simpa [prefixWord, tailWord_7132916, baseEnd_7132916] using wordTrace_append hprefix tailTrace_7132916
  have hstable : (prefixWord ++ tailWord_7132916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132916).length < 2 ^ (prefixWord ++ tailWord_7132916).sum := by decide
  have hdescent : baseEnd_7132916 < baseStart_7132916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132938 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 8]
def baseStart_7132938 : Nat := 118140960795 + 7132938 * 2 ^ 59
def prefixEnd_7132938 : Nat := 4983230072969 + 3 ^ 40 * 7132938 * 2
def baseEnd_7132938 : Nat := 406958408080013175663469

theorem tailTrace_7132938 : CollatzResearch.WordTrace tailWord_7132938 prefixEnd_7132938 406958408080013175663469 := by
  unfold tailWord_7132938
  simp only [CollatzResearch.WordTrace]
  refine ⟨65039905458147827417237867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173439747888394206445967645 65039905458147827417237867)
  ·
    refine ⟨97559858187221741125856801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65039905458147827417237867 97559858187221741125856801)
    ·
      refine ⟨73169893640416305844392601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97559858187221741125856801 73169893640416305844392601)
      ·
        refine ⟨54877420230312229383294451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73169893640416305844392601 54877420230312229383294451)
        ·
          refine ⟨82316130345468344074941677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54877420230312229383294451 82316130345468344074941677)
          ·
            refine ⟨30868548879550629028103129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82316130345468344074941677 30868548879550629028103129)
            ·
              refine ⟨23151411659662971771077347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30868548879550629028103129 23151411659662971771077347)
              ·
                refine ⟨34727117489494457656616021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23151411659662971771077347 34727117489494457656616021)
                ·
                  refine ⟨406958408080013175663469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34727117489494457656616021 406958408080013175663469)
                  ·
                    rfl

theorem cell23_7132938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 8].length) (baseStart_7132938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132938 prefixEnd_7132938 := by exact prefixLift 7132938
  have htrace : WordTrace (prefixWord ++ tailWord_7132938) baseStart_7132938 baseEnd_7132938 := by
    simpa [prefixWord, tailWord_7132938, baseEnd_7132938] using wordTrace_append hprefix tailTrace_7132938
  have hstable : (prefixWord ++ tailWord_7132938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132938).length < 2 ^ (prefixWord ++ tailWord_7132938).sum := by decide
  have hdescent : baseEnd_7132938 < baseStart_7132938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132942 : List Nat := [4, 1, 1, 2, 1, 1, 2, 6, 1, 4]
def baseStart_7132942 : Nat := 118140960795 + 7132942 * 2 ^ 59
def prefixEnd_7132942 : Nat := 4983230072969 + 3 ^ 40 * 7132942 * 2
def baseEnd_7132942 : Nat := 1220875908880912188440401

theorem tailTrace_7132942 : CollatzResearch.WordTrace tailWord_7132942 prefixEnd_7132942 1220875908880912188440401 := by
  unfold tailWord_7132942
  simp only [CollatzResearch.WordTrace]
  refine ⟨32519970965572102294012135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173439845149717878901398053 32519970965572102294012135)
  ·
    refine ⟨48779956448358153441018203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32519970965572102294012135 48779956448358153441018203)
    ·
      refine ⟨73169934672537230161527305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48779956448358153441018203 73169934672537230161527305)
      ·
        refine ⟨54877451004402922621145479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73169934672537230161527305 54877451004402922621145479)
        ·
          refine ⟨82316176506604383931718219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54877451004402922621145479 82316176506604383931718219)
          ·
            refine ⟨123474264759906575897577329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82316176506604383931718219 123474264759906575897577329)
            ·
              refine ⟨92605698569929931923182997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123474264759906575897577329 92605698569929931923182997)
              ·
                refine ⟨4340892120465465558899203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92605698569929931923182997 4340892120465465558899203)
                ·
                  refine ⟨6511338180698198338348805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340892120465465558899203 6511338180698198338348805)
                  ·
                    refine ⟨1220875908880912188440401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6511338180698198338348805 1220875908880912188440401)
                    ·
                      rfl

theorem cell23_7132942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_7132942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132942 prefixEnd_7132942 := by exact prefixLift 7132942
  have htrace : WordTrace (prefixWord ++ tailWord_7132942) baseStart_7132942 baseEnd_7132942 := by
    simpa [prefixWord, tailWord_7132942, baseEnd_7132942] using wordTrace_append hprefix tailTrace_7132942
  have hstable : (prefixWord ++ tailWord_7132942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132942).length < 2 ^ (prefixWord ++ tailWord_7132942).sum := by decide
  have hdescent : baseEnd_7132942 < baseStart_7132942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132975 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 6, 3, 2]
def baseStart_7132975 : Nat := 118140960795 + 7132975 * 2 ^ 59
def prefixEnd_7132975 : Nat := 4983230072969 + 3 ^ 40 * 7132975 * 2
def baseEnd_7132975 : Nat := 3662644671504334936208551

theorem tailTrace_7132975 : CollatzResearch.WordTrace tailWord_7132975 prefixEnd_7132975 3662644671504334936208551 := by
  unfold tailWord_7132975
  simp only [CollatzResearch.WordTrace]
  refine ⟨260160971333457264988048379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173440647555638176658698919 260160971333457264988048379)
  ·
    refine ⟨390241457000185897482072569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260160971333457264988048379 390241457000185897482072569)
    ·
      refine ⟨292681092750139423111554427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390241457000185897482072569 292681092750139423111554427)
      ·
        refine ⟨439021639125209134667331641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292681092750139423111554427 439021639125209134667331641)
        ·
          refine ⟨329266229343906851000498731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439021639125209134667331641 329266229343906851000498731)
          ·
            refine ⟨493899344015860276500748097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329266229343906851000498731 493899344015860276500748097)
            ·
              refine ⟨370424508011895207375561073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493899344015860276500748097 370424508011895207375561073)
              ·
                refine ⟨277818381008921405531670805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370424508011895207375561073 277818381008921405531670805)
                ·
                  refine ⟨13022736609793190884297069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 277818381008921405531670805 13022736609793190884297069)
                  ·
                    refine ⟨4883526228672446581611401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13022736609793190884297069 4883526228672446581611401)
                    ·
                      refine ⟨3662644671504334936208551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4883526228672446581611401 3662644671504334936208551)
                      ·
                        rfl

theorem cell23_7132975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 3, 2].length) (baseStart_7132975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132975 prefixEnd_7132975 := by exact prefixLift 7132975
  have htrace : WordTrace (prefixWord ++ tailWord_7132975) baseStart_7132975 baseEnd_7132975 := by
    simpa [prefixWord, tailWord_7132975, baseEnd_7132975] using wordTrace_append hprefix tailTrace_7132975
  have hstable : (prefixWord ++ tailWord_7132975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132975).length < 2 ^ (prefixWord ++ tailWord_7132975).sum := by decide
  have hdescent : baseEnd_7132975 < baseStart_7132975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133008 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 5]
def baseStart_7133008 : Nat := 118140960795 + 7133008 * 2 ^ 59
def prefixEnd_7133008 : Nat := 4983230072969 + 3 ^ 40 * 7133008 * 2
def baseEnd_7133008 : Nat := 3662661616365933307095899

theorem tailTrace_7133008 : CollatzResearch.WordTrace tailWord_7133008 prefixEnd_7133008 3662661616365933307095899 := by
  unfold tailWord_7133008
  simp only [CollatzResearch.WordTrace]
  refine ⟨130081087471168855811999839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173441449961558474415999785 130081087471168855811999839)
  ·
    refine ⟨195121631206753283717999759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130081087471168855811999839 195121631206753283717999759)
    ·
      refine ⟨292682446810129925576999639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195121631206753283717999759 292682446810129925576999639)
      ·
        refine ⟨439023670215194888365499459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292682446810129925576999639 439023670215194888365499459)
        ·
          refine ⟨658535505322792332548249189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439023670215194888365499459 658535505322792332548249189)
          ·
            refine ⟨123475407248023562352796723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 658535505322792332548249189 123475407248023562352796723)
            ·
              refine ⟨185213110872035343529195085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123475407248023562352796723 185213110872035343529195085)
              ·
                refine ⟨69454916577013253823448157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185213110872035343529195085 69454916577013253823448157)
                ·
                  refine ⟨26045593716379970183793059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69454916577013253823448157 26045593716379970183793059)
                  ·
                    refine ⟨39068390574569955275689589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26045593716379970183793059 39068390574569955275689589)
                    ·
                      refine ⟨3662661616365933307095899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39068390574569955275689589 3662661616365933307095899)
                      ·
                        rfl

theorem cell23_7133008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_7133008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133008 prefixEnd_7133008 := by exact prefixLift 7133008
  have htrace : WordTrace (prefixWord ++ tailWord_7133008) baseStart_7133008 baseEnd_7133008 := by
    simpa [prefixWord, tailWord_7133008, baseEnd_7133008] using wordTrace_append hprefix tailTrace_7133008
  have hstable : (prefixWord ++ tailWord_7133008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133008).length < 2 ^ (prefixWord ++ tailWord_7133008).sum := by decide
  have hdescent : baseEnd_7133008 < baseStart_7133008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133025 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 3, 2, 3]
def baseStart_7133025 : Nat := 118140960795 + 7133025 * 2 ^ 59
def prefixEnd_7133025 : Nat := 4983230072969 + 3 ^ 40 * 7133025 * 2
def baseEnd_7133025 : Nat := 3662670345537059740583321

theorem tailTrace_7133025 : CollatzResearch.WordTrace tailWord_7133025 prefixEnd_7133025 3662670345537059740583321 := by
  unfold tailWord_7133025
  simp only [CollatzResearch.WordTrace]
  refine ⟨260162794983276123527368529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173441863322184082351579019 260162794983276123527368529)
  ·
    refine ⟨195122096237457092645526397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260162794983276123527368529 195122096237457092645526397)
    ·
      refine ⟨73170786089046409742072399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195122096237457092645526397 73170786089046409742072399)
      ·
        refine ⟨109756179133569614613108599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73170786089046409742072399 109756179133569614613108599)
        ·
          refine ⟨164634268700354421919662899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109756179133569614613108599 164634268700354421919662899)
          ·
            refine ⟨246951403050531632879494349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164634268700354421919662899 246951403050531632879494349)
            ·
              refine ⟨92606776143949362329810381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246951403050531632879494349 92606776143949362329810381)
              ·
                refine ⟨34727541053981010873678893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92606776143949362329810381 34727541053981010873678893)
                ·
                  refine ⟨13022827895242879077629585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34727541053981010873678893 13022827895242879077629585)
                  ·
                    refine ⟨9767120921432159308222189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13022827895242879077629585 9767120921432159308222189)
                    ·
                      refine ⟨3662670345537059740583321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9767120921432159308222189 3662670345537059740583321)
                      ·
                        rfl

theorem cell23_7133025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_7133025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133025 prefixEnd_7133025 := by exact prefixLift 7133025
  have htrace : WordTrace (prefixWord ++ tailWord_7133025) baseStart_7133025 baseEnd_7133025 := by
    simpa [prefixWord, tailWord_7133025, baseEnd_7133025] using wordTrace_append hprefix tailTrace_7133025
  have hstable : (prefixWord ++ tailWord_7133025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133025).length < 2 ^ (prefixWord ++ tailWord_7133025).sum := by decide
  have hdescent : baseEnd_7133025 < baseStart_7133025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133026 : List Nat := [3, 3, 2, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_7133026 : Nat := 118140960795 + 7133026 * 2 ^ 59
def prefixEnd_7133026 : Nat := 4983230072969 + 3 ^ 40 * 7133026 * 2
def baseEnd_7133026 : Nat := 3662670859017714236670817

theorem tailTrace_7133026 : CollatzResearch.WordTrace tailWord_7133026 prefixEnd_7133026 3662670859017714236670817 := by
  unfold tailWord_7133026
  simp only [CollatzResearch.WordTrace]
  refine ⟨65040707864068125174538733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173441887637515000465436621 65040707864068125174538733)
  ·
    refine ⟨24390265449025546940452025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65040707864068125174538733 24390265449025546940452025)
    ·
      refine ⟨18292699086769160205339019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24390265449025546940452025 18292699086769160205339019)
      ·
        refine ⟨27439048630153740308008529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18292699086769160205339019 27439048630153740308008529)
        ·
          refine ⟨20579286472615305231006397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27439048630153740308008529 20579286472615305231006397)
          ·
            refine ⟨7717232427230739461627399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20579286472615305231006397 7717232427230739461627399)
            ·
              refine ⟨11575848640846109192441099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7717232427230739461627399 11575848640846109192441099)
              ·
                refine ⟨17363772961269163788661649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11575848640846109192441099 17363772961269163788661649)
                ·
                  refine ⟨13022829720951872841496237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17363772961269163788661649 13022829720951872841496237)
                  ·
                    refine ⟨4883561145356952315561089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13022829720951872841496237 4883561145356952315561089)
                    ·
                      refine ⟨3662670859017714236670817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4883561145356952315561089 3662670859017714236670817)
                      ·
                        rfl

theorem cell23_7133026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_7133026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133026 prefixEnd_7133026 := by exact prefixLift 7133026
  have htrace : WordTrace (prefixWord ++ tailWord_7133026) baseStart_7133026 baseEnd_7133026 := by
    simpa [prefixWord, tailWord_7133026, baseEnd_7133026] using wordTrace_append hprefix tailTrace_7133026
  have hstable : (prefixWord ++ tailWord_7133026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133026).length < 2 ^ (prefixWord ++ tailWord_7133026).sum := by decide
  have hdescent : baseEnd_7133026 < baseStart_7133026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133066 : List Nat := [3, 1, 2, 4, 2, 1, 3, 1, 2, 4]
def baseStart_7133066 : Nat := 118140960795 + 7133066 * 2 ^ 59
def prefixEnd_7133066 : Nat := 4983230072969 + 3 ^ 40 * 7133066 * 2
def baseEnd_7133066 : Nat := 1220897132747964693390211

theorem tailTrace_7133066 : CollatzResearch.WordTrace tailWord_7133066 prefixEnd_7133066 1220897132747964693390211 := by
  unfold tailWord_7133066
  simp only [CollatzResearch.WordTrace]
  refine ⟨65041072594031896882402763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173442860250751725019740701 65041072594031896882402763)
  ·
    refine ⟨97561608891047845323604145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65041072594031896882402763 97561608891047845323604145)
    ·
      refine ⟨73171206668285883992703109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97561608891047845323604145 73171206668285883992703109)
      ·
        refine ⟨13719601250303603248631833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73171206668285883992703109 13719601250303603248631833)
        ·
          refine ⟨10289700937727702436473875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13719601250303603248631833 10289700937727702436473875)
          ·
            refine ⟨15434551406591553654710813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10289700937727702436473875 15434551406591553654710813)
            ·
              refine ⟨5787956777471832620516555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15434551406591553654710813 5787956777471832620516555)
              ·
                refine ⟨8681935166207748930774833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5787956777471832620516555 8681935166207748930774833)
                ·
                  refine ⟨6511451374655811698081125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8681935166207748930774833 6511451374655811698081125)
                  ·
                    refine ⟨1220897132747964693390211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6511451374655811698081125 1220897132747964693390211)
                    ·
                      rfl

theorem cell23_7133066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_7133066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133066 prefixEnd_7133066 := by exact prefixLift 7133066
  have htrace : WordTrace (prefixWord ++ tailWord_7133066) baseStart_7133066 baseEnd_7133066 := by
    simpa [prefixWord, tailWord_7133066, baseEnd_7133066] using wordTrace_append hprefix tailTrace_7133066
  have hstable : (prefixWord ++ tailWord_7133066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133066).length < 2 ^ (prefixWord ++ tailWord_7133066).sum := by decide
  have hdescent : baseEnd_7133066 < baseStart_7133066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133085 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_7133085 : Nat := 118140960795 + 7133085 * 2 ^ 59
def prefixEnd_7133085 : Nat := 4983230072969 + 3 ^ 40 * 7133085 * 2
def baseEnd_7133085 : Nat := 3662701154376329505833045

theorem tailTrace_7133085 : CollatzResearch.WordTrace tailWord_7133085 prefixEnd_7133085 3662701154376329505833045 := by
  unfold tailWord_7133085
  simp only [CollatzResearch.WordTrace]
  refine ⟨260164983363058753774552709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173443322242039169183035139 260164983363058753774552709)
  ·
    refine ⟨48780934380573516332728633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260164983363058753774552709 48780934380573516332728633)
    ·
      refine ⟨36585700785430137249546475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48780934380573516332728633 36585700785430137249546475)
      ·
        refine ⟨54878551178145205874319713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36585700785430137249546475 54878551178145205874319713)
        ·
          refine ⟨41158913383608904405739785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54878551178145205874319713 41158913383608904405739785)
          ·
            refine ⟨30869185037706678304304839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41158913383608904405739785 30869185037706678304304839)
            ·
              refine ⟨46303777556560017456457259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30869185037706678304304839 46303777556560017456457259)
              ·
                refine ⟨69455666334840026184685889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46303777556560017456457259 69455666334840026184685889)
                ·
                  refine ⟨52091749751130019638514417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69455666334840026184685889 52091749751130019638514417)
                  ·
                    refine ⟨39068812313347514728885813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52091749751130019638514417 39068812313347514728885813)
                    ·
                      refine ⟨3662701154376329505833045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39068812313347514728885813 3662701154376329505833045)
                      ·
                        rfl

theorem cell23_7133085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_7133085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133085 prefixEnd_7133085 := by exact prefixLift 7133085
  have htrace : WordTrace (prefixWord ++ tailWord_7133085) baseStart_7133085 baseEnd_7133085 := by
    simpa [prefixWord, tailWord_7133085, baseEnd_7133085] using wordTrace_append hprefix tailTrace_7133085
  have hstable : (prefixWord ++ tailWord_7133085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133085).length < 2 ^ (prefixWord ++ tailWord_7133085).sum := by decide
  have hdescent : baseEnd_7133085 < baseStart_7133085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133090 : List Nat := [3, 3, 1, 2, 3, 2, 1, 3, 1, 2, 2]
def baseStart_7133090 : Nat := 118140960795 + 7133090 * 2 ^ 59
def prefixEnd_7133090 : Nat := 4983230072969 + 3 ^ 40 * 7133090 * 2
def baseEnd_7133090 : Nat := 3662703721779601986270523

theorem tailTrace_7133090 : CollatzResearch.WordTrace tailWord_7133090 prefixEnd_7133090 3662703721779601986270523 := by
  unfold tailWord_7133090
  simp only [CollatzResearch.WordTrace]
  refine ⟨65041291432010159907121181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173443443818693759752323149 65041291432010159907121181)
  ·
    refine ⟨24390484287003809965170443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65041291432010159907121181 24390484287003809965170443)
    ·
      refine ⟨36585726430505714947755665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24390484287003809965170443 36585726430505714947755665)
      ·
        refine ⟨27439294822879286210816749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36585726430505714947755665 27439294822879286210816749)
        ·
          refine ⟨10289735558579732329056281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27439294822879286210816749 10289735558579732329056281)
          ·
            refine ⟨7717301668934799246792211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10289735558579732329056281 7717301668934799246792211)
            ·
              refine ⟨11575952503402198870188317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7717301668934799246792211 11575952503402198870188317)
              ·
                refine ⟨4340982188775824576320619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11575952503402198870188317 4340982188775824576320619)
                ·
                  refine ⟨6511473283163736864480929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340982188775824576320619 6511473283163736864480929)
                  ·
                    refine ⟨4883604962372802648360697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6511473283163736864480929 4883604962372802648360697)
                    ·
                      refine ⟨3662703721779601986270523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4883604962372802648360697 3662703721779601986270523)
                      ·
                        rfl

theorem cell23_7133090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_7133090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133090 prefixEnd_7133090 := by exact prefixLift 7133090
  have htrace : WordTrace (prefixWord ++ tailWord_7133090) baseStart_7133090 baseEnd_7133090 := by
    simpa [prefixWord, tailWord_7133090, baseEnd_7133090] using wordTrace_append hprefix tailTrace_7133090
  have hstable : (prefixWord ++ tailWord_7133090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133090).length < 2 ^ (prefixWord ++ tailWord_7133090).sum := by decide
  have hdescent : baseEnd_7133090 < baseStart_7133090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133129 : List Nat := [1, 2, 1, 1, 2, 1, 2, 7, 2, 2, 2]
def baseStart_7133129 : Nat := 118140960795 + 7133129 * 2 ^ 59
def prefixEnd_7133129 : Nat := 4983230072969 + 3 ^ 40 * 7133129 * 2
def baseEnd_7133129 : Nat := 3662723747525127333682843

theorem tailTrace_7133129 : CollatzResearch.WordTrace tailWord_7133129 prefixEnd_7133129 3662723747525127333682843 := by
  unfold tailWord_7133129
  simp only [CollatzResearch.WordTrace]
  refine ⟨260166588174899349289154441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173444392116599566192769627 260166588174899349289154441)
  ·
    refine ⟨195124941131174511966865831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260166588174899349289154441 195124941131174511966865831)
    ·
      refine ⟨292687411696761767950298747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195124941131174511966865831 292687411696761767950298747)
      ·
        refine ⟨439031117545142651925448121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292687411696761767950298747 439031117545142651925448121)
        ·
          refine ⟨329273338158856988944086091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439031117545142651925448121 329273338158856988944086091)
          ·
            refine ⟨493910007238285483416129137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329273338158856988944086091 493910007238285483416129137)
            ·
              refine ⟨370432505428714112562096853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493910007238285483416129137 370432505428714112562096853)
              ·
                refine ⟨8682011845985487013174145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 370432505428714112562096853 8682011845985487013174145)
                ·
                  refine ⟨6511508884489115259880609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8682011845985487013174145 6511508884489115259880609)
                  ·
                    refine ⟨4883631663366836444910457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6511508884489115259880609 4883631663366836444910457)
                    ·
                      refine ⟨3662723747525127333682843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4883631663366836444910457 3662723747525127333682843)
                      ·
                        rfl

theorem cell23_7133129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 2, 2].length) (baseStart_7133129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133129 prefixEnd_7133129 := by exact prefixLift 7133129
  have htrace : WordTrace (prefixWord ++ tailWord_7133129) baseStart_7133129 baseEnd_7133129 := by
    simpa [prefixWord, tailWord_7133129, baseEnd_7133129] using wordTrace_append hprefix tailTrace_7133129
  have hstable : (prefixWord ++ tailWord_7133129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133129).length < 2 ^ (prefixWord ++ tailWord_7133129).sum := by decide
  have hdescent : baseEnd_7133129 < baseStart_7133129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133162 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_7133162 : Nat := 118140960795 + 7133162 * 2 ^ 59
def prefixEnd_7133162 : Nat := 4983230072969 + 3 ^ 40 * 7133162 * 2
def baseEnd_7133162 : Nat := 3662740692386725704570191

theorem tailTrace_7133162 : CollatzResearch.WordTrace tailWord_7133162 prefixEnd_7133162 3662740692386725704570191 := by
  unfold tailWord_7133162
  simp only [CollatzResearch.WordTrace]
  refine ⟨65041947945944948981276435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173445194522519863950070493 65041947945944948981276435)
  ·
    refine ⟨97562921918917423471914653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65041947945944948981276435 97562921918917423471914653)
    ·
      refine ⟨36586095719594033801967995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97562921918917423471914653 36586095719594033801967995)
      ·
        refine ⟨54879143579391050702951993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36586095719594033801967995 54879143579391050702951993)
        ·
          refine ⟨41159357684543288027213995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54879143579391050702951993 41159357684543288027213995)
          ·
            refine ⟨61739036526814932040820993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41159357684543288027213995 61739036526814932040820993)
            ·
              refine ⟨46304277395111199030615745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61739036526814932040820993 46304277395111199030615745)
              ·
                refine ⟨34728208046333399272961809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46304277395111199030615745 34728208046333399272961809)
                ·
                  refine ⟨26046156034750049454721357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34728208046333399272961809 26046156034750049454721357)
                  ·
                    refine ⟨9767308513031268545520509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26046156034750049454721357 9767308513031268545520509)
                    ·
                      refine ⟨3662740692386725704570191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9767308513031268545520509 3662740692386725704570191)
                      ·
                        rfl

theorem cell23_7133162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_7133162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133162 prefixEnd_7133162 := by exact prefixLift 7133162
  have htrace : WordTrace (prefixWord ++ tailWord_7133162) baseStart_7133162 baseEnd_7133162 := by
    simpa [prefixWord, tailWord_7133162, baseEnd_7133162] using wordTrace_append hprefix tailTrace_7133162
  have hstable : (prefixWord ++ tailWord_7133162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133162).length < 2 ^ (prefixWord ++ tailWord_7133162).sum := by decide
  have hdescent : baseEnd_7133162 < baseStart_7133162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133169 : List Nat := [1, 2, 2, 2, 5, 1, 1, 4, 5]
def baseStart_7133169 : Nat := 118140960795 + 7133169 * 2 ^ 59
def prefixEnd_7133169 : Nat := 4983230072969 + 3 ^ 40 * 7133169 * 2
def baseEnd_7133169 : Nat := 406971587416811908575851

theorem tailTrace_7133169 : CollatzResearch.WordTrace tailWord_7133169 prefixEnd_7133169 406971587416811908575851 := by
  unfold tailWord_7133169
  simp only [CollatzResearch.WordTrace]
  refine ⟨260168047094754436120610561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173445364729836290747073707 260168047094754436120610561)
  ·
    refine ⟨195126035321065827090457921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260168047094754436120610561 195126035321065827090457921)
    ·
      refine ⟨146344526490799370317843441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195126035321065827090457921 146344526490799370317843441)
      ·
        refine ⟨109758394868099527738382581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146344526490799370317843441 109758394868099527738382581)
        ·
          refine ⟨10289849518884330725473367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109758394868099527738382581 10289849518884330725473367)
          ·
            refine ⟨15434774278326496088210051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10289849518884330725473367 15434774278326496088210051)
            ·
              refine ⟨23152161417489744132315077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15434774278326496088210051 23152161417489744132315077)
              ·
                refine ⟨4341030265779327024809077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23152161417489744132315077 4341030265779327024809077)
                ·
                  refine ⟨406971587416811908575851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4341030265779327024809077 406971587416811908575851)
                  ·
                    rfl

theorem cell23_7133169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 5].length) (baseStart_7133169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133169 prefixEnd_7133169 := by exact prefixLift 7133169
  have htrace : WordTrace (prefixWord ++ tailWord_7133169) baseStart_7133169 baseEnd_7133169 := by
    simpa [prefixWord, tailWord_7133169, baseEnd_7133169] using wordTrace_append hprefix tailTrace_7133169
  have hstable : (prefixWord ++ tailWord_7133169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133169).length < 2 ^ (prefixWord ++ tailWord_7133169).sum := by decide
  have hdescent : baseEnd_7133169 < baseStart_7133169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133215 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 6]
def baseStart_7133215 : Nat := 118140960795 + 7133215 * 2 ^ 59
def prefixEnd_7133215 : Nat := 4983230072969 + 3 ^ 40 * 7133215 * 2
def baseEnd_7133215 : Nat := 3662767906861413997207447

theorem tailTrace_7133215 : CollatzResearch.WordTrace tailWord_7133215 prefixEnd_7133215 3662767906861413997207447 := by
  unfold tailWord_7133215
  simp only [CollatzResearch.WordTrace]
  refine ⟨260169724852587785976785099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173446483235058523984523399 260169724852587785976785099)
  ·
    refine ⟨390254587278881678965177649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260169724852587785976785099 390254587278881678965177649)
    ·
      refine ⟨292690940459161259223883237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390254587278881678965177649 292690940459161259223883237)
      ·
        refine ⟨54879551336092736104478107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292690940459161259223883237 54879551336092736104478107)
        ·
          refine ⟨82319327004139104156717161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54879551336092736104478107 82319327004139104156717161)
          ·
            refine ⟨61739495253104328117537871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82319327004139104156717161 61739495253104328117537871)
            ·
              refine ⟨92609242879656492176306807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61739495253104328117537871 92609242879656492176306807)
              ·
                refine ⟨138913864319484738264460211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92609242879656492176306807 138913864319484738264460211)
                ·
                  refine ⟨208370796479227107396690317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138913864319484738264460211 208370796479227107396690317)
                  ·
                    refine ⟨78139048679710165273758869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 208370796479227107396690317 78139048679710165273758869)
                    ·
                      refine ⟨3662767906861413997207447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78139048679710165273758869 3662767906861413997207447)
                      ·
                        rfl

theorem cell23_7133215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_7133215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133215 prefixEnd_7133215 := by exact prefixLift 7133215
  have htrace : WordTrace (prefixWord ++ tailWord_7133215) baseStart_7133215 baseEnd_7133215 := by
    simpa [prefixWord, tailWord_7133215, baseEnd_7133215] using wordTrace_append hprefix tailTrace_7133215
  have hstable : (prefixWord ++ tailWord_7133215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133215).length < 2 ^ (prefixWord ++ tailWord_7133215).sum := by decide
  have hdescent : baseEnd_7133215 < baseStart_7133215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133309 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_7133309 : Nat := 118140960795 + 7133309 * 2 ^ 59
def prefixEnd_7133309 : Nat := 4983230072969 + 3 ^ 40 * 7133309 * 2
def baseEnd_7133309 : Nat := 3662816174042936629432015

theorem tailTrace_7133309 : CollatzResearch.WordTrace tailWord_7133309 prefixEnd_7133309 3662816174042936629432015 := by
  unfold tailWord_7133309
  simp only [CollatzResearch.WordTrace]
  refine ⟨260173153314247240030706981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173448768876164826687137987 260173153314247240030706981)
  ·
    refine ⟨48782466246421357505757559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260173153314247240030706981 48782466246421357505757559)
    ·
      refine ⟨73173699369632036258636339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48782466246421357505757559 73173699369632036258636339)
      ·
        refine ⟨109760549054448054387954509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73173699369632036258636339 109760549054448054387954509)
        ·
          refine ⟨41160205895418020395482941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109760549054448054387954509 41160205895418020395482941)
          ·
            refine ⟨15435077210781757648306103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41160205895418020395482941 15435077210781757648306103)
            ·
              refine ⟨23152615816172636472459155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15435077210781757648306103 23152615816172636472459155)
              ·
                refine ⟨34728923724258954708688733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23152615816172636472459155 34728923724258954708688733)
                ·
                  refine ⟨13023346396597108015758275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34728923724258954708688733 13023346396597108015758275)
                  ·
                    refine ⟨19535019594895662023637413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13023346396597108015758275 19535019594895662023637413)
                    ·
                      refine ⟨3662816174042936629432015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19535019594895662023637413 3662816174042936629432015)
                      ·
                        rfl

theorem cell23_7133309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_7133309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133309 prefixEnd_7133309 := by exact prefixLift 7133309
  have htrace : WordTrace (prefixWord ++ tailWord_7133309) baseStart_7133309 baseEnd_7133309 := by
    simpa [prefixWord, tailWord_7133309, baseEnd_7133309] using wordTrace_append hprefix tailTrace_7133309
  have hstable : (prefixWord ++ tailWord_7133309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133309).length < 2 ^ (prefixWord ++ tailWord_7133309).sum := by decide
  have hdescent : baseEnd_7133309 < baseStart_7133309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133313 : List Nat := [1, 2, 4, 2, 3, 1, 2, 1, 2, 3, 2]
def baseStart_7133313 : Nat := 118140960795 + 7133313 * 2 ^ 59
def prefixEnd_7133313 : Nat := 4983230072969 + 3 ^ 40 * 7133313 * 2
def baseEnd_7133313 : Nat := 3662818227965554613781997

theorem tailTrace_7133313 : CollatzResearch.WordTrace tailWord_7133313 prefixEnd_7133313 3662818227965554613781997 := by
  unfold tailWord_7133313
  simp only [CollatzResearch.WordTrace]
  refine ⟨260173299206232748713852593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173448866137488499142568395 260173299206232748713852593)
  ·
    refine ⟨195129974404674561535389445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260173299206232748713852593 195129974404674561535389445)
    ·
      refine ⟨36586870200876480287885521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195129974404674561535389445 36586870200876480287885521)
      ·
        refine ⟨27440152650657360215914141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36586870200876480287885521 27440152650657360215914141)
        ·
          refine ⟨10290057243996510080967803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27440152650657360215914141 10290057243996510080967803)
          ·
            refine ⟨15435085865994765121451705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10290057243996510080967803 15435085865994765121451705)
            ·
              refine ⟨11576314399496073841088779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15435085865994765121451705 11576314399496073841088779)
              ·
                refine ⟨17364471599244110761633169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11576314399496073841088779 17364471599244110761633169)
                ·
                  refine ⟨13023353699433083071224877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17364471599244110761633169 13023353699433083071224877)
                  ·
                    refine ⟨4883757637287406151709329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13023353699433083071224877 4883757637287406151709329)
                    ·
                      refine ⟨3662818227965554613781997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4883757637287406151709329 3662818227965554613781997)
                      ·
                        rfl

theorem cell23_7133313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_7133313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133313 prefixEnd_7133313 := by exact prefixLift 7133313
  have htrace : WordTrace (prefixWord ++ tailWord_7133313) baseStart_7133313 baseEnd_7133313 := by
    simpa [prefixWord, tailWord_7133313, baseEnd_7133313] using wordTrace_append hprefix tailTrace_7133313
  have hstable : (prefixWord ++ tailWord_7133313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133313).length < 2 ^ (prefixWord ++ tailWord_7133313).sum := by decide
  have hdescent : baseEnd_7133313 < baseStart_7133313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133346 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_7133346 : Nat := 118140960795 + 7133346 * 2 ^ 59
def prefixEnd_7133346 : Nat := 4983230072969 + 3 ^ 40 * 7133346 * 2
def baseEnd_7133346 : Nat := 3662835172827152984669345

theorem tailTrace_7133346 : CollatzResearch.WordTrace tailWord_7133346 prefixEnd_7133346 3662835172827152984669345 := by
  unfold tailWord_7133346
  simp only [CollatzResearch.WordTrace]
  refine ⟨65043625703778298837450973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173449668543408796899869261 65043625703778298837450973)
  ·
    refine ⟨24391359638916862064044115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65043625703778298837450973 24391359638916862064044115)
    ·
      refine ⟨36587039458375293096066173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24391359638916862064044115 36587039458375293096066173)
      ·
        refine ⟨13720139796890734911024815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36587039458375293096066173 13720139796890734911024815)
        ·
          refine ⟨20580209695336102366537223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13720139796890734911024815 20580209695336102366537223)
          ·
            refine ⟨30870314543004153549805835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20580209695336102366537223 30870314543004153549805835)
            ·
              refine ⟨46305471814506230324708753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30870314543004153549805835 46305471814506230324708753)
              ·
                refine ⟨34729103860879672743531565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46305471814506230324708753 34729103860879672743531565)
                ·
                  refine ⟨13023413947829877278824337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34729103860879672743531565 13023413947829877278824337)
                  ·
                    refine ⟨9767560460872407959118253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13023413947829877278824337 9767560460872407959118253)
                    ·
                      refine ⟨3662835172827152984669345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9767560460872407959118253 3662835172827152984669345)
                      ·
                        rfl

theorem cell23_7133346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_7133346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133346 prefixEnd_7133346 := by exact prefixLift 7133346
  have htrace : WordTrace (prefixWord ++ tailWord_7133346) baseStart_7133346 baseEnd_7133346 := by
    simpa [prefixWord, tailWord_7133346, baseEnd_7133346] using wordTrace_append hprefix tailTrace_7133346
  have hstable : (prefixWord ++ tailWord_7133346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133346).length < 2 ^ (prefixWord ++ tailWord_7133346).sum := by decide
  have hdescent : baseEnd_7133346 < baseStart_7133346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133359 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 6, 1, 3]
def baseStart_7133359 : Nat := 118140960795 + 7133359 * 2 ^ 59
def prefixEnd_7133359 : Nat := 4983230072969 + 3 ^ 40 * 7133359 * 2
def baseEnd_7133359 : Nat := 3662841848075661433806785

theorem tailTrace_7133359 : CollatzResearch.WordTrace tailWord_7133359 prefixEnd_7133359 3662841848075661433806785 := by
  unfold tailWord_7133359
  simp only [CollatzResearch.WordTrace]
  refine ⟨260174976964066098570027131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173449984642710732380018087 260174976964066098570027131)
  ·
    refine ⟨390262465446099147855040697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260174976964066098570027131 390262465446099147855040697)
    ·
      refine ⟨292696849084574360891280523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390262465446099147855040697 292696849084574360891280523)
      ·
        refine ⟨439045273626861541336920785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292696849084574360891280523 439045273626861541336920785)
        ·
          refine ⟨329283955220146156002690589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439045273626861541336920785 329283955220146156002690589)
          ·
            refine ⟨123481483207554808501008971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329283955220146156002690589 123481483207554808501008971)
            ·
              refine ⟨185222224811332212751513457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123481483207554808501008971 185222224811332212751513457)
              ·
                refine ⟨138916668608499159563635093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185222224811332212751513457 138916668608499159563635093)
                ·
                  refine ⟨6511718841023398104545395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138916668608499159563635093 6511718841023398104545395)
                  ·
                    refine ⟨9767578261535097156818093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6511718841023398104545395 9767578261535097156818093)
                    ·
                      refine ⟨3662841848075661433806785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9767578261535097156818093 3662841848075661433806785)
                      ·
                        rfl

theorem cell23_7133359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 1, 3].length) (baseStart_7133359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133359 prefixEnd_7133359 := by exact prefixLift 7133359
  have htrace : WordTrace (prefixWord ++ tailWord_7133359) baseStart_7133359 baseEnd_7133359 := by
    simpa [prefixWord, tailWord_7133359, baseEnd_7133359] using wordTrace_append hprefix tailTrace_7133359
  have hstable : (prefixWord ++ tailWord_7133359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133359).length < 2 ^ (prefixWord ++ tailWord_7133359).sum := by decide
  have hdescent : baseEnd_7133359 < baseStart_7133359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133362 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 2, 7]
def baseStart_7133362 : Nat := 118140960795 + 7133362 * 2 ^ 59
def prefixEnd_7133362 : Nat := 4983230072969 + 3 ^ 40 * 7133362 * 2
def baseEnd_7133362 : Nat := 1220947796172541640689757

theorem tailTrace_7133362 : CollatzResearch.WordTrace tailWord_7133362 prefixEnd_7133362 1220947796172541640689757 := by
  unfold tailWord_7133362
  simp only [CollatzResearch.WordTrace]
  refine ⟨65043771595763807520596585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173450057588703486721590893 65043771595763807520596585)
  ·
    refine ⟨48782828696822855640447439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65043771595763807520596585 48782828696822855640447439)
    ·
      refine ⟨73174243045234283460671159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48782828696822855640447439 73174243045234283460671159)
      ·
        refine ⟨109761364567851425191006739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73174243045234283460671159 109761364567851425191006739)
        ·
          refine ⟨164642046851777137786510109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109761364567851425191006739 164642046851777137786510109)
          ·
            refine ⟨61740767569416426669941291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164642046851777137786510109 61740767569416426669941291)
            ·
              refine ⟨92611151354124640004911937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61740767569416426669941291 92611151354124640004911937)
              ·
                refine ⟨69458363515593480003683953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92611151354124640004911937 69458363515593480003683953)
                ·
                  refine ⟨52093772636695110002762965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69458363515593480003683953 52093772636695110002762965)
                  ·
                    refine ⟨1220947796172541640689757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52093772636695110002762965 1220947796172541640689757)
                    ·
                      rfl

theorem cell23_7133362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_7133362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133362 prefixEnd_7133362 := by exact prefixLift 7133362
  have htrace : WordTrace (prefixWord ++ tailWord_7133362) baseStart_7133362 baseEnd_7133362 := by
    simpa [prefixWord, tailWord_7133362, baseEnd_7133362] using wordTrace_append hprefix tailTrace_7133362
  have hstable : (prefixWord ++ tailWord_7133362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133362).length < 2 ^ (prefixWord ++ tailWord_7133362).sum := by decide
  have hdescent : baseEnd_7133362 < baseStart_7133362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133364 : List Nat := [2, 5, 3, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_7133364 : Nat := 118140960795 + 7133364 * 2 ^ 59
def prefixEnd_7133364 : Nat := 4983230072969 + 3 ^ 40 * 7133364 * 2
def baseEnd_7133364 : Nat := 3662844415478933914244263

theorem tailTrace_7133364 : CollatzResearch.WordTrace tailWord_7133364 prefixEnd_7133364 3662844415478933914244263 := by
  unfold tailWord_7133364
  simp only [CollatzResearch.WordTrace]
  refine ⟨130087579664523992211979573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173450106219365322949306097 130087579664523992211979573)
  ·
    refine ⟨12195710593549124269873085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130087579664523992211979573 12195710593549124269873085)
    ·
      refine ⟨4573391472580921601202407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12195710593549124269873085 4573391472580921601202407)
      ·
        refine ⟨6860087208871382401803611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4573391472580921601202407 6860087208871382401803611)
        ·
          refine ⟨10290130813307073602705417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6860087208871382401803611 10290130813307073602705417)
          ·
            refine ⟨7717598109980305202029063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10290130813307073602705417 7717598109980305202029063)
            ·
              refine ⟨11576397164970457803043595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7717598109980305202029063 11576397164970457803043595)
              ·
                refine ⟨17364595747455686704565393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11576397164970457803043595 17364595747455686704565393)
                ·
                  refine ⟨13023446810591765028424045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17364595747455686704565393 13023446810591765028424045)
                  ·
                    refine ⟨4883792553971911885659017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13023446810591765028424045 4883792553971911885659017)
                    ·
                      refine ⟨3662844415478933914244263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4883792553971911885659017 3662844415478933914244263)
                      ·
                        rfl

theorem cell23_7133364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_7133364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133364 prefixEnd_7133364 := by exact prefixLift 7133364
  have htrace : WordTrace (prefixWord ++ tailWord_7133364) baseStart_7133364 baseEnd_7133364 := by
    simpa [prefixWord, tailWord_7133364, baseEnd_7133364] using wordTrace_append hprefix tailTrace_7133364
  have hstable : (prefixWord ++ tailWord_7133364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133364).length < 2 ^ (prefixWord ++ tailWord_7133364).sum := by decide
  have hdescent : baseEnd_7133364 < baseStart_7133364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133377 : List Nat := [1, 2, 6, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_7133377 : Nat := 118140960795 + 7133377 * 2 ^ 59
def prefixEnd_7133377 : Nat := 4983230072969 + 3 ^ 40 * 7133377 * 2
def baseEnd_7133377 : Nat := 3662851090727442363381703

theorem tailTrace_7133377 : CollatzResearch.WordTrace tailWord_7133377 prefixEnd_7133377 3662851090727442363381703 := by
  unfold tailWord_7133377
  simp only [CollatzResearch.WordTrace]
  refine ⟨260175633478000887644182385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173450422318667258429454923 260175633478000887644182385)
  ·
    refine ⟨195131725108500665733136789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260175633478000887644182385 195131725108500665733136789)
    ·
      refine ⟨9146799614460968706240787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 195131725108500665733136789 9146799614460968706240787)
      ·
        refine ⟨13720199421691453059361181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9146799614460968706240787 13720199421691453059361181)
        ·
          refine ⟨5145074783134294897260443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13720199421691453059361181 5145074783134294897260443)
          ·
            refine ⟨7717612174701442345890665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5145074783134294897260443 7717612174701442345890665)
            ·
              refine ⟨5788209131026081759417999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7717612174701442345890665 5788209131026081759417999)
              ·
                refine ⟨8682313696539122639126999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5788209131026081759417999 8682313696539122639126999)
                ·
                  refine ⟨13023470544808683958690499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8682313696539122639126999 13023470544808683958690499)
                  ·
                    refine ⟨19535205817213025938035749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13023470544808683958690499 19535205817213025938035749)
                    ·
                      refine ⟨3662851090727442363381703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19535205817213025938035749 3662851090727442363381703)
                      ·
                        rfl

theorem cell23_7133377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_7133377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133377 prefixEnd_7133377 := by exact prefixLift 7133377
  have htrace : WordTrace (prefixWord ++ tailWord_7133377) baseStart_7133377 baseEnd_7133377 := by
    simpa [prefixWord, tailWord_7133377, baseEnd_7133377] using wordTrace_append hprefix tailTrace_7133377
  have hstable : (prefixWord ++ tailWord_7133377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133377).length < 2 ^ (prefixWord ++ tailWord_7133377).sum := by decide
  have hdescent : baseEnd_7133377 < baseStart_7133377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133380 : List Nat := [2, 3, 3, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_7133380 : Nat := 118140960795 + 7133380 * 2 ^ 59
def prefixEnd_7133380 : Nat := 4983230072969 + 3 ^ 40 * 7133380 * 2
def baseEnd_7133380 : Nat := 3662852631169405851644189

theorem tailTrace_7133380 : CollatzResearch.WordTrace tailWord_7133380 prefixEnd_7133380 3662852631169405851644189 := by
  unfold tailWord_7133380
  simp only [CollatzResearch.WordTrace]
  refine ⟨130087871448495009578270797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173450495264660012771027729 130087871448495009578270797)
  ·
    refine ⟨48782951793185628591851549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130087871448495009578270797 48782951793185628591851549)
    ·
      refine ⟨18293606922444610721944331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48782951793185628591851549 18293606922444610721944331)
      ·
        refine ⟨27440410383666916082916497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18293606922444610721944331 27440410383666916082916497)
        ·
          refine ⟨20580307787750187062187373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27440410383666916082916497 20580307787750187062187373)
          ·
            refine ⟨7717615420406320148320265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20580307787750187062187373 7717615420406320148320265)
            ·
              refine ⟨5788211565304740111240199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7717615420406320148320265 5788211565304740111240199)
              ·
                refine ⟨8682317347957110166860299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5788211565304740111240199 8682317347957110166860299)
                ·
                  refine ⟨13023476021935665250290449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8682317347957110166860299 13023476021935665250290449)
                  ·
                    refine ⟨9767607016451748937717837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13023476021935665250290449 9767607016451748937717837)
                    ·
                      refine ⟨3662852631169405851644189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9767607016451748937717837 3662852631169405851644189)
                      ·
                        rfl

theorem cell23_7133380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_7133380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133380 prefixEnd_7133380 := by exact prefixLift 7133380
  have htrace : WordTrace (prefixWord ++ tailWord_7133380) baseStart_7133380 baseEnd_7133380 := by
    simpa [prefixWord, tailWord_7133380, baseEnd_7133380] using wordTrace_append hprefix tailTrace_7133380
  have hstable : (prefixWord ++ tailWord_7133380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133380).length < 2 ^ (prefixWord ++ tailWord_7133380).sum := by decide
  have hdescent : baseEnd_7133380 < baseStart_7133380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133509 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 5, 4, 3]
def baseStart_7133509 : Nat := 118140960795 + 7133509 * 2 ^ 59
def prefixEnd_7133509 : Nat := 4983230072969 + 3 ^ 40 * 7133509 * 2
def baseEnd_7133509 : Nat := 3662918870173835846931095

theorem tailTrace_7133509 : CollatzResearch.WordTrace tailWord_7133509 prefixEnd_7133509 3662918870173835846931095 := by
  unfold tailWord_7133509
  simp only [CollatzResearch.WordTrace]
  refine ⟨260180447913522674187987581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173453631942348449458658387 260180447913522674187987581)
  ·
    refine ⟨97567667967571002820495343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260180447913522674187987581 97567667967571002820495343)
    ·
      refine ⟨146351501951356504230743015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97567667967571002820495343 146351501951356504230743015)
      ·
        refine ⟨219527252927034756346114523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146351501951356504230743015 219527252927034756346114523)
        ·
          refine ⟨329290879390552134519171785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219527252927034756346114523 329290879390552134519171785)
          ·
            refine ⟨246968159542914100889378839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329290879390552134519171785 246968159542914100889378839)
            ·
              refine ⟨370452239314371151334068259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246968159542914100889378839 370452239314371151334068259)
              ·
                refine ⟨555678358971556727001102389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370452239314371151334068259 555678358971556727001102389)
                ·
                  refine ⟨52094846153583443156353349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 555678358971556727001102389 52094846153583443156353349)
                  ·
                    refine ⟨9767783653796895591816253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52094846153583443156353349 9767783653796895591816253)
                    ·
                      refine ⟨3662918870173835846931095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9767783653796895591816253 3662918870173835846931095)
                      ·
                        rfl

theorem cell23_7133509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_7133509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133509 prefixEnd_7133509 := by exact prefixLift 7133509
  have htrace : WordTrace (prefixWord ++ tailWord_7133509) baseStart_7133509 baseEnd_7133509 := by
    simpa [prefixWord, tailWord_7133509, baseEnd_7133509] using wordTrace_append hprefix tailTrace_7133509
  have hstable : (prefixWord ++ tailWord_7133509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133509).length < 2 ^ (prefixWord ++ tailWord_7133509).sum := by decide
  have hdescent : baseEnd_7133509 < baseStart_7133509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133516 : List Nat := [2, 2, 1, 3, 2, 1, 2, 3, 3, 4]
def baseStart_7133516 : Nat := 118140960795 + 7133516 * 2 ^ 59
def prefixEnd_7133516 : Nat := 4983230072969 + 3 ^ 40 * 7133516 * 2
def baseEnd_7133516 : Nat := 1220974154846139106514521

theorem tailTrace_7133516 : CollatzResearch.WordTrace tailWord_7133516 prefixEnd_7133516 1220974154846139106514521 := by
  unfold tailWord_7133516
  simp only [CollatzResearch.WordTrace]
  refine ⟨130090351612248657191746201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173453802149664876255661601 130090351612248657191746201)
  ·
    refine ⟨97567763709186492893809651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130090351612248657191746201 97567763709186492893809651)
    ·
      refine ⟨146351645563779739340714477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97567763709186492893809651 146351645563779739340714477)
      ·
        refine ⟨54881867086417402252767929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146351645563779739340714477 54881867086417402252767929)
        ·
          refine ⟨41161400314813051689575947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54881867086417402252767929 41161400314813051689575947)
          ·
            refine ⟨61742100472219577534363921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41161400314813051689575947 61742100472219577534363921)
            ·
              refine ⟨46306575354164683150772941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61742100472219577534363921 46306575354164683150772941)
              ·
                refine ⟨17364965757811756181539853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46306575354164683150772941 17364965757811756181539853)
                ·
                  refine ⟨6511862159179408568077445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17364965757811756181539853 6511862159179408568077445)
                  ·
                    refine ⟨1220974154846139106514521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6511862159179408568077445 1220974154846139106514521)
                    ·
                      rfl

theorem cell23_7133516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_7133516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133516 prefixEnd_7133516 := by exact prefixLift 7133516
  have htrace : WordTrace (prefixWord ++ tailWord_7133516) baseStart_7133516 baseEnd_7133516 := by
    simpa [prefixWord, tailWord_7133516, baseEnd_7133516] using wordTrace_append hprefix tailTrace_7133516
  have hstable : (prefixWord ++ tailWord_7133516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133516).length < 2 ^ (prefixWord ++ tailWord_7133516).sum := by decide
  have hdescent : baseEnd_7133516 < baseStart_7133516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133543 : List Nat := [1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_7133543 : Nat := 118140960795 + 7133543 * 2 ^ 59
def prefixEnd_7133543 : Nat := 4983230072969 + 3 ^ 40 * 7133543 * 2
def baseEnd_7133543 : Nat := 3662936328516088713905939

theorem tailTrace_7133543 : CollatzResearch.WordTrace tailWord_7133543 prefixEnd_7133543 3662936328516088713905939 := by
  unfold tailWord_7133543
  simp only [CollatzResearch.WordTrace]
  refine ⟨260181687995399497994725283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173454458663599665329816855 260181687995399497994725283)
  ·
    refine ⟨390272531993099246992087925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260181687995399497994725283 390272531993099246992087925)
    ·
      refine ⟨36588049874353054405508243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 390272531993099246992087925 36588049874353054405508243)
      ·
        refine ⟨54882074811529581608262365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36588049874353054405508243 54882074811529581608262365)
        ·
          refine ⟨20580778054323593103098387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54882074811529581608262365 20580778054323593103098387)
          ·
            refine ⟨30871167081485389654647581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20580778054323593103098387 30871167081485389654647581)
            ·
              refine ⟨11576687655557021120492843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30871167081485389654647581 11576687655557021120492843)
              ·
                refine ⟨17365031483335531680739265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11576687655557021120492843 17365031483335531680739265)
                ·
                  refine ⟨13023773612501648760554449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17365031483335531680739265 13023773612501648760554449)
                  ·
                    refine ⟨9767830209376236570415837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13023773612501648760554449 9767830209376236570415837)
                    ·
                      refine ⟨3662936328516088713905939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9767830209376236570415837 3662936328516088713905939)
                      ·
                        rfl

theorem cell23_7133543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_7133543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133543 prefixEnd_7133543 := by exact prefixLift 7133543
  have htrace : WordTrace (prefixWord ++ tailWord_7133543) baseStart_7133543 baseEnd_7133543 := by
    simpa [prefixWord, tailWord_7133543, baseEnd_7133543] using wordTrace_append hprefix tailTrace_7133543
  have hstable : (prefixWord ++ tailWord_7133543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133543).length < 2 ^ (prefixWord ++ tailWord_7133543).sum := by decide
  have hdescent : baseEnd_7133543 < baseStart_7133543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133559 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 5, 5]
def baseStart_7133559 : Nat := 118140960795 + 7133559 * 2 ^ 59
def prefixEnd_7133559 : Nat := 4983230072969 + 3 ^ 40 * 7133559 * 2
def baseEnd_7133559 : Nat := 1220981514735520217101955

theorem tailTrace_7133559 : CollatzResearch.WordTrace tailWord_7133559 prefixEnd_7133559 1220981514735520217101955 := by
  unfold tailWord_7133559
  simp only [CollatzResearch.WordTrace]
  refine ⟨260182271563341532727307731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173454847708894355151538487 260182271563341532727307731)
  ·
    refine ⟨390273407345012299090961597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260182271563341532727307731 390273407345012299090961597)
    ·
      refine ⟨146352527754379612159110599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390273407345012299090961597 146352527754379612159110599)
      ·
        refine ⟨219528791631569418238665899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146352527754379612159110599 219528791631569418238665899)
        ·
          refine ⟨329293187447354127357998849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219528791631569418238665899 329293187447354127357998849)
          ·
            refine ⟨246969890585515595518499137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329293187447354127357998849 246969890585515595518499137)
            ·
              refine ⟨185227417939136696638874353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246969890585515595518499137 185227417939136696638874353)
              ·
                refine ⟨138920563454352522479155765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185227417939136696638874353 138920563454352522479155765)
                ·
                  refine ⟨13023802823845548982420853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138920563454352522479155765 13023802823845548982420853)
                  ·
                    refine ⟨1220981514735520217101955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13023802823845548982420853 1220981514735520217101955)
                    ·
                      rfl

theorem cell23_7133559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_7133559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133559 prefixEnd_7133559 := by exact prefixLift 7133559
  have htrace : WordTrace (prefixWord ++ tailWord_7133559) baseStart_7133559 baseEnd_7133559 := by
    simpa [prefixWord, tailWord_7133559, baseEnd_7133559] using wordTrace_append hprefix tailTrace_7133559
  have hstable : (prefixWord ++ tailWord_7133559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133559).length < 2 ^ (prefixWord ++ tailWord_7133559).sum := by decide
  have hdescent : baseEnd_7133559 < baseStart_7133559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133607 : List Nat := [1, 1, 6, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_7133607 : Nat := 118140960795 + 7133607 * 2 ^ 59
def prefixEnd_7133607 : Nat := 4983230072969 + 3 ^ 40 * 7133607 * 2
def baseEnd_7133607 : Nat := 3662969191277976463505645

theorem tailTrace_7133607 : CollatzResearch.WordTrace tailWord_7133607 prefixEnd_7133607 3662969191277976463505645 := by
  unfold tailWord_7133607
  simp only [CollatzResearch.WordTrace]
  refine ⟨260184022267167636925055075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173456014844778424616703383 260184022267167636925055075)
  ·
    refine ⟨390276033400751455387582613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260184022267167636925055075 390276033400751455387582613)
    ·
      refine ⟨18294189065660224471292935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 390276033400751455387582613 18294189065660224471292935)
      ·
        refine ⟨27441283598490336706939403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18294189065660224471292935 27441283598490336706939403)
        ·
          refine ⟨41161925397735505060409105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27441283598490336706939403 41161925397735505060409105)
          ·
            refine ⟨30871444048301628795306829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41161925397735505060409105 30871444048301628795306829)
            ·
              refine ⟨11576791518113110798240061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30871444048301628795306829 11576791518113110798240061)
              ·
                refine ⟨4341296819292416549340023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11576791518113110798240061 4341296819292416549340023)
                ·
                  refine ⟨6511945228938624824010035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4341296819292416549340023 6511945228938624824010035)
                  ·
                    refine ⟨9767917843407937236015053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6511945228938624824010035 9767917843407937236015053)
                    ·
                      refine ⟨3662969191277976463505645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9767917843407937236015053 3662969191277976463505645)
                      ·
                        rfl

theorem cell23_7133607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_7133607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133607 prefixEnd_7133607 := by exact prefixLift 7133607
  have htrace : WordTrace (prefixWord ++ tailWord_7133607) baseStart_7133607 baseEnd_7133607 := by
    simpa [prefixWord, tailWord_7133607, baseEnd_7133607] using wordTrace_append hprefix tailTrace_7133607
  have hstable : (prefixWord ++ tailWord_7133607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133607).length < 2 ^ (prefixWord ++ tailWord_7133607).sum := by decide
  have hdescent : baseEnd_7133607 < baseStart_7133607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133640 : List Nat := [2, 1, 3, 1, 3, 2, 4, 1, 2, 4]
def baseStart_7133640 : Nat := 118140960795 + 7133640 * 2 ^ 59
def prefixEnd_7133640 : Nat := 4983230072969 + 3 ^ 40 * 7133640 * 2
def baseEnd_7133640 : Nat := 1220995378713191611464331

theorem tailTrace_7133640 : CollatzResearch.WordTrace tailWord_7133640 prefixEnd_7133640 1220995378713191611464331 := by
  unfold tailWord_7133640
  simp only [CollatzResearch.WordTrace]
  refine ⟨130092612938024041780503187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173456817250698722374004249 130092612938024041780503187)
  ·
    refine ⟨195138919407036062670754781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130092612938024041780503187 195138919407036062670754781)
    ·
      refine ⟨73177094777638523501533043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195138919407036062670754781 73177094777638523501533043)
      ·
        refine ⟨109765642166457785252299565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73177094777638523501533043 109765642166457785252299565)
        ·
          refine ⟨41162115812421669469612337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109765642166457785252299565 41162115812421669469612337)
          ·
            refine ⟨30871586859316252102209253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41162115812421669469612337 30871586859316252102209253)
            ·
              refine ⟨5788422536121797269164235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30871586859316252102209253 5788422536121797269164235)
              ·
                refine ⟨8682633804182695903746353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5788422536121797269164235 8682633804182695903746353)
                ·
                  refine ⟨6511975353137021927809765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8682633804182695903746353 6511975353137021927809765)
                  ·
                    refine ⟨1220995378713191611464331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6511975353137021927809765 1220995378713191611464331)
                    ·
                      rfl

theorem cell23_7133640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_7133640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133640 prefixEnd_7133640 := by exact prefixLift 7133640
  have htrace : WordTrace (prefixWord ++ tailWord_7133640) baseStart_7133640 baseEnd_7133640 := by
    simpa [prefixWord, tailWord_7133640, baseEnd_7133640] using wordTrace_append hprefix tailTrace_7133640
  have hstable : (prefixWord ++ tailWord_7133640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133640).length < 2 ^ (prefixWord ++ tailWord_7133640).sum := by decide
  have hdescent : baseEnd_7133640 < baseStart_7133640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133663 : List Nat := [1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 3]
def baseStart_7133663 : Nat := 118140960795 + 7133663 * 2 ^ 59
def prefixEnd_7133663 : Nat := 4983230072969 + 3 ^ 40 * 7133663 * 2
def baseEnd_7133663 : Nat := 3662997946194628244405387

theorem tailTrace_7133663 : CollatzResearch.WordTrace tailWord_7133663 prefixEnd_7133663 3662997946194628244405387 := by
  unfold tailWord_7133663
  simp only [CollatzResearch.WordTrace]
  refine ⟨260186064754964758489093643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173457376503309838992729095 260186064754964758489093643)
  ·
    refine ⟨390279097132447137733640465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260186064754964758489093643 390279097132447137733640465)
    ·
      refine ⟨292709322849335353300230349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390279097132447137733640465 292709322849335353300230349)
      ·
        refine ⟨109765996068500757487586381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292709322849335353300230349 109765996068500757487586381)
        ·
          refine ⟨41162248525687784057844893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109765996068500757487586381 41162248525687784057844893)
          ·
            refine ⟨15435843197132919021691835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41162248525687784057844893 15435843197132919021691835)
            ·
              refine ⟨23153764795699378532537753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15435843197132919021691835 23153764795699378532537753)
              ·
                refine ⟨17365323596774533899403315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23153764795699378532537753 17365323596774533899403315)
                ·
                  refine ⟨26047985395161800849104973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17365323596774533899403315 26047985395161800849104973)
                  ·
                    refine ⟨9767994523185675318414365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26047985395161800849104973 9767994523185675318414365)
                    ·
                      refine ⟨3662997946194628244405387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9767994523185675318414365 3662997946194628244405387)
                      ·
                        rfl

theorem cell23_7133663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_7133663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133663 prefixEnd_7133663 := by exact prefixLift 7133663
  have htrace : WordTrace (prefixWord ++ tailWord_7133663) baseStart_7133663 baseEnd_7133663 := by
    simpa [prefixWord, tailWord_7133663, baseEnd_7133663] using wordTrace_append hprefix tailTrace_7133663
  have hstable : (prefixWord ++ tailWord_7133663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133663).length < 2 ^ (prefixWord ++ tailWord_7133663).sum := by decide
  have hdescent : baseEnd_7133663 < baseStart_7133663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133667 : List Nat := [1, 1, 1, 6, 3, 1, 3, 1, 1, 2, 3]
def baseStart_7133667 : Nat := 118140960795 + 7133667 * 2 ^ 59
def prefixEnd_7133667 : Nat := 4983230072969 + 3 ^ 40 * 7133667 * 2
def baseEnd_7133667 : Nat := 3663000000117246228755369

theorem tailTrace_7133667 : CollatzResearch.WordTrace tailWord_7133667 prefixEnd_7133667 3663000000117246228755369 := by
  unfold tailWord_7133667
  simp only [CollatzResearch.WordTrace]
  refine ⟨260186210646950267172239255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173457473764633511448159503 260186210646950267172239255)
  ·
    refine ⟨390279315970425400758358883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260186210646950267172239255 390279315970425400758358883)
    ·
      refine ⟨585418973955638101137538325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390279315970425400758358883 585418973955638101137538325)
      ·
        refine ⟨27441514404170535990822109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 585418973955638101137538325 27441514404170535990822109)
        ·
          refine ⟨10290567901563950996558291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27441514404170535990822109 10290567901563950996558291)
          ·
            refine ⟨15435851852345926494837437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10290567901563950996558291 15435851852345926494837437)
            ·
              refine ⟨5788444444629722435564039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15435851852345926494837437 5788444444629722435564039)
              ·
                refine ⟨8682666666944583653346059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5788444444629722435564039 8682666666944583653346059)
                ·
                  refine ⟨13024000000416875480019089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8682666666944583653346059 13024000000416875480019089)
                  ·
                    refine ⟨9768000000312656610014317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13024000000416875480019089 9768000000312656610014317)
                    ·
                      refine ⟨3663000000117246228755369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9768000000312656610014317 3663000000117246228755369)
                      ·
                        rfl

theorem cell23_7133667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_7133667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133667 prefixEnd_7133667 := by exact prefixLift 7133667
  have htrace : WordTrace (prefixWord ++ tailWord_7133667) baseStart_7133667 baseEnd_7133667 := by
    simpa [prefixWord, tailWord_7133667, baseEnd_7133667] using wordTrace_append hprefix tailTrace_7133667
  have hstable : (prefixWord ++ tailWord_7133667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133667).length < 2 ^ (prefixWord ++ tailWord_7133667).sum := by decide
  have hdescent : baseEnd_7133667 < baseStart_7133667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133680 : List Nat := [2, 1, 1, 1, 3, 3, 4, 2, 2, 1, 3]
def baseStart_7133680 : Nat := 118140960795 + 7133680 * 2 ^ 59
def prefixEnd_7133680 : Nat := 4983230072969 + 3 ^ 40 * 7133680 * 2
def baseEnd_7133680 : Nat := 3663006675365754677892809

theorem tailTrace_7133680 : CollatzResearch.WordTrace tailWord_7133680 prefixEnd_7133680 3663006675365754677892809 := by
  unfold tailWord_7133680
  simp only [CollatzResearch.WordTrace]
  refine ⟨130093342397951585196231247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173457789863935446928308329 130093342397951585196231247)
  ·
    refine ⟨195140013596927377794346871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130093342397951585196231247 195140013596927377794346871)
    ·
      refine ⟨292710020395391066691520307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195140013596927377794346871 292710020395391066691520307)
      ·
        refine ⟨439065030593086600037280461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292710020395391066691520307 439065030593086600037280461)
        ·
          refine ⟨164649386472407475013980173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 439065030593086600037280461 164649386472407475013980173)
          ·
            refine ⟨61743519927152803130242565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164649386472407475013980173 61743519927152803130242565)
            ·
              refine ⟨11576909986341150586920481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61743519927152803130242565 11576909986341150586920481)
              ·
                refine ⟨8682682489755862940190361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11576909986341150586920481 8682682489755862940190361)
                ·
                  refine ⟨6512011867316897205142771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8682682489755862940190361 6512011867316897205142771)
                  ·
                    refine ⟨9768017800975345807714157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6512011867316897205142771 9768017800975345807714157)
                    ·
                      refine ⟨3663006675365754677892809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9768017800975345807714157 3663006675365754677892809)
                      ·
                        rfl

theorem cell23_7133680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 2, 1, 3].length) (baseStart_7133680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133680 prefixEnd_7133680 := by exact prefixLift 7133680
  have htrace : WordTrace (prefixWord ++ tailWord_7133680) baseStart_7133680 baseEnd_7133680 := by
    simpa [prefixWord, tailWord_7133680, baseEnd_7133680] using wordTrace_append hprefix tailTrace_7133680
  have hstable : (prefixWord ++ tailWord_7133680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133680).length < 2 ^ (prefixWord ++ tailWord_7133680).sum := by decide
  have hdescent : baseEnd_7133680 < baseStart_7133680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133720 : List Nat := [2, 1, 2, 3, 3, 1, 2, 2, 1, 4, 2]
def baseStart_7133720 : Nat := 118140960795 + 7133720 * 2 ^ 59
def prefixEnd_7133720 : Nat := 4983230072969 + 3 ^ 40 * 7133720 * 2
def baseEnd_7133720 : Nat := 3663027214591934521392625

theorem tailTrace_7133720 : CollatzResearch.WordTrace tailWord_7133720 prefixEnd_7133720 3663027214591934521392625 := by
  unfold tailWord_7133720
  simp only [CollatzResearch.WordTrace]
  refine ⟨130094071857879128611959307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173458762477172171482612409 130094071857879128611959307)
  ·
    refine ⟨195141107786818692917938961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130094071857879128611959307 195141107786818692917938961)
    ·
      refine ⟨146355830840114019688454221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195141107786818692917938961 146355830840114019688454221)
      ·
        refine ⟨54883436565042757383170333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146355830840114019688454221 54883436565042757383170333)
        ·
          refine ⟨20581288711891034018688875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54883436565042757383170333 20581288711891034018688875)
          ·
            refine ⟨30871933067836551028033313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20581288711891034018688875 30871933067836551028033313)
            ·
              refine ⟨23153949800877413271024985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30871933067836551028033313 23153949800877413271024985)
              ·
                refine ⟨17365462350658059953268739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23153949800877413271024985 17365462350658059953268739)
                ·
                  refine ⟨26048193525987089929903109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17365462350658059953268739 26048193525987089929903109)
                  ·
                    refine ⟨4884036286122579361856833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26048193525987089929903109 4884036286122579361856833)
                    ·
                      refine ⟨3663027214591934521392625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4884036286122579361856833 3663027214591934521392625)
                      ·
                        rfl

theorem cell23_7133720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_7133720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133720 prefixEnd_7133720 := by exact prefixLift 7133720
  have htrace : WordTrace (prefixWord ++ tailWord_7133720) baseStart_7133720 baseEnd_7133720 := by
    simpa [prefixWord, tailWord_7133720, baseEnd_7133720] using wordTrace_append hprefix tailTrace_7133720
  have hstable : (prefixWord ++ tailWord_7133720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133720).length < 2 ^ (prefixWord ++ tailWord_7133720).sum := by decide
  have hdescent : baseEnd_7133720 < baseStart_7133720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133724 : List Nat := [2, 2, 3, 1, 2, 4, 2, 1, 1, 3, 2]
def baseStart_7133724 : Nat := 118140960795 + 7133724 * 2 ^ 59
def prefixEnd_7133724 : Nat := 4983230072969 + 3 ^ 40 * 7133724 * 2
def baseEnd_7133724 : Nat := 3663029268514552505742607

theorem tailTrace_7133724 : CollatzResearch.WordTrace tailWord_7133724 prefixEnd_7133724 3663029268514552505742607 := by
  unfold tailWord_7133724
  simp only [CollatzResearch.WordTrace]
  refine ⟨130094144803871882953532113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173458859738495843938042817 130094144803871882953532113)
  ·
    refine ⟨97570608602903912215149085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130094144803871882953532113 97570608602903912215149085)
    ·
      refine ⟨36588978226088967080680907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97570608602903912215149085 36588978226088967080680907)
      ·
        refine ⟨54883467339133450621021361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36588978226088967080680907 54883467339133450621021361)
        ·
          refine ⟨41162600504350087965766021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54883467339133450621021361 41162600504350087965766021)
          ·
            refine ⟨7717987594565641493581129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41162600504350087965766021 7717987594565641493581129)
            ·
              refine ⟨5788490695924231120185847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7717987594565641493581129 5788490695924231120185847)
              ·
                refine ⟨8682736043886346680278771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5788490695924231120185847 8682736043886346680278771)
                ·
                  refine ⟨13024104065829520020418157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8682736043886346680278771 13024104065829520020418157)
                  ·
                    refine ⟨4884039024686070007656809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13024104065829520020418157 4884039024686070007656809)
                    ·
                      refine ⟨3663029268514552505742607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4884039024686070007656809 3663029268514552505742607)
                      ·
                        rfl

theorem cell23_7133724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_7133724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133724 prefixEnd_7133724 := by exact prefixLift 7133724
  have htrace : WordTrace (prefixWord ++ tailWord_7133724) baseStart_7133724 baseEnd_7133724 := by
    simpa [prefixWord, tailWord_7133724, baseEnd_7133724] using wordTrace_append hprefix tailTrace_7133724
  have hstable : (prefixWord ++ tailWord_7133724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133724).length < 2 ^ (prefixWord ++ tailWord_7133724).sum := by decide
  have hdescent : baseEnd_7133724 < baseStart_7133724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133750 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_7133750 : Nat := 118140960795 + 7133750 * 2 ^ 59
def prefixEnd_7133750 : Nat := 4983230072969 + 3 ^ 40 * 7133750 * 2
def baseEnd_7133750 : Nat := 3663042619011569404017487

theorem tailTrace_7133750 : CollatzResearch.WordTrace tailWord_7133750 prefixEnd_7133750 3663042619011569404017487 := by
  unfold tailWord_7133750
  simp only [CollatzResearch.WordTrace]
  refine ⟨16261827369103098271719419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173459491937099714898340469 16261827369103098271719419)
  ·
    refine ⟨24392741053654647407579129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16261827369103098271719419 24392741053654647407579129)
    ·
      refine ⟨18294555790240985555684347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24392741053654647407579129 18294555790240985555684347)
      ·
        refine ⟨27441833685361478333526521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18294555790240985555684347 27441833685361478333526521)
        ·
          refine ⟨20581375264021108750144891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27441833685361478333526521 20581375264021108750144891)
          ·
            refine ⟨30872062896031663125217337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20581375264021108750144891 30872062896031663125217337)
            ·
              refine ⟨23154047172023747343913003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30872062896031663125217337 23154047172023747343913003)
              ·
                refine ⟨34731070758035621015869505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23154047172023747343913003 34731070758035621015869505)
                ·
                  refine ⟨26048303068526715761902129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34731070758035621015869505 26048303068526715761902129)
                  ·
                    refine ⟨19536227301395036821426597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26048303068526715761902129 19536227301395036821426597)
                    ·
                      refine ⟨3663042619011569404017487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19536227301395036821426597 3663042619011569404017487)
                      ·
                        rfl

theorem cell23_7133750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_7133750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133750 prefixEnd_7133750 := by exact prefixLift 7133750
  have htrace : WordTrace (prefixWord ++ tailWord_7133750) baseStart_7133750 baseEnd_7133750 := by
    simpa [prefixWord, tailWord_7133750, baseEnd_7133750] using wordTrace_append hprefix tailTrace_7133750
  have hstable : (prefixWord ++ tailWord_7133750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133750).length < 2 ^ (prefixWord ++ tailWord_7133750).sum := by decide
  have hdescent : baseEnd_7133750 < baseStart_7133750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133753 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 2, 3, 3]
def baseStart_7133753 : Nat := 118140960795 + 7133753 * 2 ^ 59
def prefixEnd_7133753 : Nat := 4983230072969 + 3 ^ 40 * 7133753 * 2
def baseEnd_7133753 : Nat := 3663044159453532892279973

theorem tailTrace_7133753 : CollatzResearch.WordTrace tailWord_7133753 prefixEnd_7133753 3663044159453532892279973 := by
  unfold tailWord_7133753
  simp only [CollatzResearch.WordTrace]
  refine ⟨260189347324638703859869913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173459564883092469239913275 260189347324638703859869913)
  ·
    refine ⟨195142010493479027894902435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260189347324638703859869913 195142010493479027894902435)
    ·
      refine ⟨292713015740218541842353653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195142010493479027894902435 292713015740218541842353653)
      ·
        refine ⟨27441845225645488297720655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 292713015740218541842353653 27441845225645488297720655)
        ·
          refine ⟨41162767838468232446580983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27441845225645488297720655 41162767838468232446580983)
          ·
            refine ⟨61744151757702348669871475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41162767838468232446580983 61744151757702348669871475)
            ·
              refine ⟨92616227636553523004807213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61744151757702348669871475 92616227636553523004807213)
              ·
                refine ⟨34731085363707571126802705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92616227636553523004807213 34731085363707571126802705)
                ·
                  refine ⟨26048314022780678345102029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34731085363707571126802705 26048314022780678345102029)
                  ·
                    refine ⟨9768117758542754379413261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26048314022780678345102029 9768117758542754379413261)
                    ·
                      refine ⟨3663044159453532892279973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9768117758542754379413261 3663044159453532892279973)
                      ·
                        rfl

theorem cell23_7133753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_7133753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133753 prefixEnd_7133753 := by exact prefixLift 7133753
  have htrace : WordTrace (prefixWord ++ tailWord_7133753) baseStart_7133753 baseEnd_7133753 := by
    simpa [prefixWord, tailWord_7133753, baseEnd_7133753] using wordTrace_append hprefix tailTrace_7133753
  have hstable : (prefixWord ++ tailWord_7133753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133753).length < 2 ^ (prefixWord ++ tailWord_7133753).sum := by decide
  have hdescent : baseEnd_7133753 < baseStart_7133753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133754 : List Nat := [3, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2]
def baseStart_7133754 : Nat := 118140960795 + 7133754 * 2 ^ 59
def prefixEnd_7133754 : Nat := 4983230072969 + 3 ^ 40 * 7133754 * 2
def baseEnd_7133754 : Nat := 3663044672934187388367469

theorem tailTrace_7133754 : CollatzResearch.WordTrace tailWord_7133754 prefixEnd_7133754 3663044672934187388367469 := by
  unfold tailWord_7133754
  simp only [CollatzResearch.WordTrace]
  refine ⟨65047345949408770257664079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173459589198423387353770877 65047345949408770257664079)
  ·
    refine ⟨97571018924113155386496119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65047345949408770257664079 97571018924113155386496119)
    ·
      refine ⟨146356528386169733079744179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97571018924113155386496119 146356528386169733079744179)
      ·
        refine ⟨219534792579254599619616269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146356528386169733079744179 219534792579254599619616269)
        ·
          refine ⟨82325547217220474857356101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219534792579254599619616269 82325547217220474857356101)
          ·
            refine ⟨15436040103228839035754269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82325547217220474857356101 15436040103228839035754269)
            ·
              refine ⟨5788515038710814638407851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15436040103228839035754269 5788515038710814638407851)
              ·
                refine ⟨8682772558066221957611777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5788515038710814638407851 8682772558066221957611777)
                ·
                  refine ⟨6512079418549666468208833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8682772558066221957611777 6512079418549666468208833)
                  ·
                    refine ⟨4884059563912249851156625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6512079418549666468208833 4884059563912249851156625)
                    ·
                      refine ⟨3663044672934187388367469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4884059563912249851156625 3663044672934187388367469)
                      ·
                        rfl

theorem cell23_7133754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2].length) (baseStart_7133754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133754 prefixEnd_7133754 := by exact prefixLift 7133754
  have htrace : WordTrace (prefixWord ++ tailWord_7133754) baseStart_7133754 baseEnd_7133754 := by
    simpa [prefixWord, tailWord_7133754, baseEnd_7133754] using wordTrace_append hprefix tailTrace_7133754
  have hstable : (prefixWord ++ tailWord_7133754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133754).length < 2 ^ (prefixWord ++ tailWord_7133754).sum := by decide
  have hdescent : baseEnd_7133754 < baseStart_7133754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133763 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 2, 5, 2]
def baseStart_7133763 : Nat := 118140960795 + 7133763 * 2 ^ 59
def prefixEnd_7133763 : Nat := 4983230072969 + 3 ^ 40 * 7133763 * 2
def baseEnd_7133763 : Nat := 3663049294260077853154927

theorem tailTrace_7133763 : CollatzResearch.WordTrace tailWord_7133763 prefixEnd_7133763 3663049294260077853154927 := by
  unfold tailWord_7133763
  simp only [CollatzResearch.WordTrace]
  refine ⟨260189712054602475567733943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173459808036401650378489295 260189712054602475567733943)
  ·
    refine ⟨390284568081903713351600915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260189712054602475567733943 390284568081903713351600915)
    ·
      refine ⟨585426852122855570027401373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390284568081903713351600915 585426852122855570027401373)
      ·
        refine ⟨219535069546070838760275515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 585426852122855570027401373 219535069546070838760275515)
        ·
          refine ⟨329302604319106258140413273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219535069546070838760275515 329302604319106258140413273)
          ·
            refine ⟨246976953239329693605309955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329302604319106258140413273 246976953239329693605309955)
            ·
              refine ⟨370465429858994540407964933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246976953239329693605309955 370465429858994540407964933)
              ·
                refine ⟨69462268098561476326493425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 370465429858994540407964933 69462268098561476326493425)
                ·
                  refine ⟨52096701073921107244870069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69462268098561476326493425 52096701073921107244870069)
                  ·
                    refine ⟨4884065725680103804206569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52096701073921107244870069 4884065725680103804206569)
                    ·
                      refine ⟨3663049294260077853154927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4884065725680103804206569 3663049294260077853154927)
                      ·
                        rfl

theorem cell23_7133763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 5, 2].length) (baseStart_7133763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133763 prefixEnd_7133763 := by exact prefixLift 7133763
  have htrace : WordTrace (prefixWord ++ tailWord_7133763) baseStart_7133763 baseEnd_7133763 := by
    simpa [prefixWord, tailWord_7133763, baseEnd_7133763] using wordTrace_append hprefix tailTrace_7133763
  have hstable : (prefixWord ++ tailWord_7133763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133763).length < 2 ^ (prefixWord ++ tailWord_7133763).sum := by decide
  have hdescent : baseEnd_7133763 < baseStart_7133763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133793 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_7133793 : Nat := 118140960795 + 7133793 * 2 ^ 59
def prefixEnd_7133793 : Nat := 4983230072969 + 3 ^ 40 * 7133793 * 2
def baseEnd_7133793 : Nat := 3663064698679712735779789

theorem tailTrace_7133793 : CollatzResearch.WordTrace tailWord_7133793 prefixEnd_7133793 3663064698679712735779789 := by
  unfold tailWord_7133793
  simp only [CollatzResearch.WordTrace]
  refine ⟨260190806244493790691326033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173460537496329193794217355 260190806244493790691326033)
  ·
    refine ⟨195143104683370343018494525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260190806244493790691326033 195143104683370343018494525)
    ·
      refine ⟨73178664256263878631935447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195143104683370343018494525 73178664256263878631935447)
      ·
        refine ⟨109767996384395817947903171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73178664256263878631935447 109767996384395817947903171)
        ·
          refine ⟨164651994576593726921854757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109767996384395817947903171 164651994576593726921854757)
          ·
            refine ⟨30872248983111323797847767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164651994576593726921854757 30872248983111323797847767)
            ·
              refine ⟨46308373474666985696771651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30872248983111323797847767 46308373474666985696771651)
              ·
                refine ⟨69462560212000478545157477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46308373474666985696771651 69462560212000478545157477)
                ·
                  refine ⟨13024230039750089727217027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69462560212000478545157477 13024230039750089727217027)
                  ·
                    refine ⟨19536345059625134590825541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13024230039750089727217027 19536345059625134590825541)
                    ·
                      refine ⟨3663064698679712735779789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19536345059625134590825541 3663064698679712735779789)
                      ·
                        rfl

theorem cell23_7133793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_7133793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133793 prefixEnd_7133793 := by exact prefixLift 7133793
  have htrace : WordTrace (prefixWord ++ tailWord_7133793) baseStart_7133793 baseEnd_7133793 := by
    simpa [prefixWord, tailWord_7133793, baseEnd_7133793] using wordTrace_append hprefix tailTrace_7133793
  have hstable : (prefixWord ++ tailWord_7133793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133793).length < 2 ^ (prefixWord ++ tailWord_7133793).sum := by decide
  have hdescent : baseEnd_7133793 < baseStart_7133793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133794 : List Nat := [3, 3, 2, 3, 2, 1, 1, 1, 7]
def baseStart_7133794 : Nat := 118140960795 + 7133794 * 2 ^ 59
def prefixEnd_7133794 : Nat := 4983230072969 + 3 ^ 40 * 7133794 * 2
def baseEnd_7133794 : Nat := 407007245795596359096365

theorem tailTrace_7133794 : CollatzResearch.WordTrace tailWord_7133794 prefixEnd_7133794 407007245795596359096365 := by
  unfold tailWord_7133794
  simp only [CollatzResearch.WordTrace]
  refine ⟨65047710679372541965528109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173460561811660111908074957 65047710679372541965528109)
  ·
    refine ⟨24392891504764703237073041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65047710679372541965528109 24392891504764703237073041)
    ·
      refine ⟨18294668628573527427804781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24392891504764703237073041 18294668628573527427804781)
      ·
        refine ⟨6860500735715072785426793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18294668628573527427804781 6860500735715072785426793)
        ·
          refine ⟨5145375551786304589070095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6860500735715072785426793 5145375551786304589070095)
          ·
            refine ⟨7718063327679456883605143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5145375551786304589070095 7718063327679456883605143)
            ·
              refine ⟨11577094991519185325407715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7718063327679456883605143 11577094991519185325407715)
              ·
                refine ⟨17365642487278777988111573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11577094991519185325407715 17365642487278777988111573)
                ·
                  refine ⟨407007245795596359096365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17365642487278777988111573 407007245795596359096365)
                  ·
                    rfl

theorem cell23_7133794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_7133794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133794 prefixEnd_7133794 := by exact prefixLift 7133794
  have htrace : WordTrace (prefixWord ++ tailWord_7133794) baseStart_7133794 baseEnd_7133794 := by
    simpa [prefixWord, tailWord_7133794, baseEnd_7133794] using wordTrace_append hprefix tailTrace_7133794
  have hstable : (prefixWord ++ tailWord_7133794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133794).length < 2 ^ (prefixWord ++ tailWord_7133794).sum := by decide
  have hdescent : baseEnd_7133794 < baseStart_7133794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133800 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_7133800 : Nat := 118140960795 + 7133800 * 2 ^ 59
def prefixEnd_7133800 : Nat := 4983230072969 + 3 ^ 40 * 7133800 * 2
def baseEnd_7133800 : Nat := 3663068293044294208392257

theorem tailTrace_7133800 : CollatzResearch.WordTrace tailWord_7133800 prefixEnd_7133800 3663068293044294208392257 := by
  unfold tailWord_7133800
  simp only [CollatzResearch.WordTrace]
  refine ⟨130095530777734215443415427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173460707703645620591220569 130095530777734215443415427)
  ·
    refine ⟨195143296166601323165123141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130095530777734215443415427 195143296166601323165123141)
    ·
      refine ⟨36589368031237748093460589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195143296166601323165123141 36589368031237748093460589)
      ·
        refine ⟨13721013011714155535047721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36589368031237748093460589 13721013011714155535047721)
        ·
          refine ⟨10290759758785616651285791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13721013011714155535047721 10290759758785616651285791)
          ·
            refine ⟨15436139638178424976928687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10290759758785616651285791 15436139638178424976928687)
            ·
              refine ⟨23154209457267637465393031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15436139638178424976928687 23154209457267637465393031)
              ·
                refine ⟨34731314185901456198089547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23154209457267637465393031 34731314185901456198089547)
                ·
                  refine ⟨52096971278852184297134321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34731314185901456198089547 52096971278852184297134321)
                  ·
                    refine ⟨39072728459139138222850741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52096971278852184297134321 39072728459139138222850741)
                    ·
                      refine ⟨3663068293044294208392257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39072728459139138222850741 3663068293044294208392257)
                      ·
                        rfl

theorem cell23_7133800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_7133800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133800 prefixEnd_7133800 := by exact prefixLift 7133800
  have htrace : WordTrace (prefixWord ++ tailWord_7133800) baseStart_7133800 baseEnd_7133800 := by
    simpa [prefixWord, tailWord_7133800, baseEnd_7133800] using wordTrace_append hprefix tailTrace_7133800
  have hstable : (prefixWord ++ tailWord_7133800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133800).length < 2 ^ (prefixWord ++ tailWord_7133800).sum := by decide
  have hdescent : baseEnd_7133800 < baseStart_7133800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133803 : List Nat := [1, 1, 1, 1, 2, 2, 1, 7, 3, 4]
def baseStart_7133803 : Nat := 118140960795 + 7133803 * 2 ^ 59
def prefixEnd_7133803 : Nat := 4983230072969 + 3 ^ 40 * 7133803 * 2
def baseEnd_7133803 : Nat := 1221023277828752565551581

theorem tailTrace_7133803 : CollatzResearch.WordTrace tailWord_7133803 prefixEnd_7133803 1221023277828752565551581 := by
  unfold tailWord_7133803
  simp only [CollatzResearch.WordTrace]
  refine ⟨260191170974457562399190063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173460780649638374932793375 260191170974457562399190063)
  ·
    refine ⟨390286756461686343598785095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260191170974457562399190063 390286756461686343598785095)
    ·
      refine ⟨585430134692529515398177643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390286756461686343598785095 585430134692529515398177643)
      ·
        refine ⟨878145202038794273097266465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585430134692529515398177643 878145202038794273097266465)
        ·
          refine ⟨658608901529095704822949849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 878145202038794273097266465 658608901529095704822949849)
          ·
            refine ⟨493956676146821778617212387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658608901529095704822949849 493956676146821778617212387)
            ·
              refine ⟨740935014220232667925818581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493956676146821778617212387 740935014220232667925818581)
              ·
                refine ⟨17365664395786703154511373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 740935014220232667925818581 17365664395786703154511373)
                ·
                  refine ⟨6512124148420013682941765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17365664395786703154511373 6512124148420013682941765)
                  ·
                    refine ⟨1221023277828752565551581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6512124148420013682941765 1221023277828752565551581)
                    ·
                      rfl

theorem cell23_7133803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 4].length) (baseStart_7133803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133803 prefixEnd_7133803 := by exact prefixLift 7133803
  have htrace : WordTrace (prefixWord ++ tailWord_7133803) baseStart_7133803 baseEnd_7133803 := by
    simpa [prefixWord, tailWord_7133803, baseEnd_7133803] using wordTrace_append hprefix tailTrace_7133803
  have hstable : (prefixWord ++ tailWord_7133803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133803).length < 2 ^ (prefixWord ++ tailWord_7133803).sum := by decide
  have hdescent : baseEnd_7133803 < baseStart_7133803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133854 : List Nat := [4, 3, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_7133854 : Nat := 118140960795 + 7133854 * 2 ^ 59
def prefixEnd_7133854 : Nat := 4983230072969 + 3 ^ 40 * 7133854 * 2
def baseEnd_7133854 : Nat := 1221032006999878999039003

theorem tailTrace_7133854 : CollatzResearch.WordTrace tailWord_7133854 prefixEnd_7133854 1221032006999878999039003 := by
  unfold tailWord_7133854
  simp only [CollatzResearch.WordTrace]
  refine ⟨32524128887159099763662077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173462020731515198739531077 32524128887159099763662077)
  ·
    refine ⟨12196548332684662411373279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32524128887159099763662077 12196548332684662411373279)
    ·
      refine ⟨18294822499026993617059919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12196548332684662411373279 18294822499026993617059919)
      ·
        refine ⟨27442233748540490425589879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18294822499026993617059919 27442233748540490425589879)
        ·
          refine ⟨41163350622810735638384819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27442233748540490425589879 41163350622810735638384819)
          ·
            refine ⟨61745025934216103457577229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41163350622810735638384819 61745025934216103457577229)
            ·
              refine ⟨23154384725331038796591461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61745025934216103457577229 23154384725331038796591461)
              ·
                refine ⟨4341447135999569774360899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23154384725331038796591461 4341447135999569774360899)
                ·
                  refine ⟨6512170703999354661541349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4341447135999569774360899 6512170703999354661541349)
                  ·
                    refine ⟨1221032006999878999039003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6512170703999354661541349 1221032006999878999039003)
                    ·
                      rfl

theorem cell23_7133854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_7133854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133854 prefixEnd_7133854 := by exact prefixLift 7133854
  have htrace : WordTrace (prefixWord ++ tailWord_7133854) baseStart_7133854 baseEnd_7133854 := by
    simpa [prefixWord, tailWord_7133854, baseEnd_7133854] using wordTrace_append hprefix tailTrace_7133854
  have hstable : (prefixWord ++ tailWord_7133854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133854).length < 2 ^ (prefixWord ++ tailWord_7133854).sum := by decide
  have hdescent : baseEnd_7133854 < baseStart_7133854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133877 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_7133877 : Nat := 118140960795 + 7133877 * 2 ^ 59
def prefixEnd_7133877 : Nat := 4983230072969 + 3 ^ 40 * 7133877 * 2
def baseEnd_7133877 : Nat := 3663107831054690407129403

theorem tailTrace_7133877 : CollatzResearch.WordTrace tailWord_7133877 prefixEnd_7133877 3663107831054690407129403 := by
  unfold tailWord_7133877
  simp only [CollatzResearch.WordTrace]
  refine ⟨260193869976189473037383885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173462579984126315358255923 260193869976189473037383885)
  ·
    refine ⟨97572701241071052389018957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260193869976189473037383885 97572701241071052389018957)
    ·
      refine ⟨36589762965401644645882109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97572701241071052389018957 36589762965401644645882109)
      ·
        refine ⟨13721161112025616742205791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36589762965401644645882109 13721161112025616742205791)
        ·
          refine ⟨20581741668038425113308687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13721161112025616742205791 20581741668038425113308687)
          ·
            refine ⟨30872612502057637669963031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20581741668038425113308687 30872612502057637669963031)
            ·
              refine ⟨46308918753086456504944547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30872612502057637669963031 46308918753086456504944547)
              ·
                refine ⟨69463378129629684757416821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46308918753086456504944547 69463378129629684757416821)
                ·
                  refine ⟨6512191699652782946007827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69463378129629684757416821 6512191699652782946007827)
                  ·
                    refine ⟨9768287549479174419011741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6512191699652782946007827 9768287549479174419011741)
                    ·
                      refine ⟨3663107831054690407129403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9768287549479174419011741 3663107831054690407129403)
                      ·
                        rfl

theorem cell23_7133877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_7133877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133877 prefixEnd_7133877 := by exact prefixLift 7133877
  have htrace : WordTrace (prefixWord ++ tailWord_7133877) baseStart_7133877 baseEnd_7133877 := by
    simpa [prefixWord, tailWord_7133877, baseEnd_7133877] using wordTrace_append hprefix tailTrace_7133877
  have hstable : (prefixWord ++ tailWord_7133877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133877).length < 2 ^ (prefixWord ++ tailWord_7133877).sum := by decide
  have hdescent : baseEnd_7133877 < baseStart_7133877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133887 : List Nat := [1, 1, 2, 2, 2, 4, 3, 1, 2, 3, 2]
def baseStart_7133887 : Nat := 118140960795 + 7133887 * 2 ^ 59
def prefixEnd_7133887 : Nat := 4983230072969 + 3 ^ 40 * 7133887 * 2
def baseEnd_7133887 : Nat := 3663112965861235368004357

theorem tailTrace_7133887 : CollatzResearch.WordTrace tailWord_7133887 prefixEnd_7133887 3663112965861235368004357 := by
  unfold tailWord_7133887
  simp only [CollatzResearch.WordTrace]
  refine ⟨260194234706153244745247915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173462823137435496496831943 260194234706153244745247915)
  ·
    refine ⟨390291352059229867117871873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260194234706153244745247915 390291352059229867117871873)
    ·
      refine ⟨292718514044422400338403905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390291352059229867117871873 292718514044422400338403905)
      ·
        refine ⟨219538885533316800253802929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292718514044422400338403905 219538885533316800253802929)
        ·
          refine ⟨164654164149987600190352197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219538885533316800253802929 164654164149987600190352197)
          ·
            refine ⟨30872655778122675035691037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164654164149987600190352197 30872655778122675035691037)
            ·
              refine ⟨11577245916796003138384139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30872655778122675035691037 11577245916796003138384139)
              ·
                refine ⟨17365868875194004707576209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11577245916796003138384139 17365868875194004707576209)
                ·
                  refine ⟨13024401656395503530682157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17365868875194004707576209 13024401656395503530682157)
                  ·
                    refine ⟨4884150621148313824005809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13024401656395503530682157 4884150621148313824005809)
                    ·
                      refine ⟨3663112965861235368004357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4884150621148313824005809 3663112965861235368004357)
                      ·
                        rfl

theorem cell23_7133887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 3, 2].length) (baseStart_7133887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133887 prefixEnd_7133887 := by exact prefixLift 7133887
  have htrace : WordTrace (prefixWord ++ tailWord_7133887) baseStart_7133887 baseEnd_7133887 := by
    simpa [prefixWord, tailWord_7133887, baseEnd_7133887] using wordTrace_append hprefix tailTrace_7133887
  have hstable : (prefixWord ++ tailWord_7133887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133887).length < 2 ^ (prefixWord ++ tailWord_7133887).sum := by decide
  have hdescent : baseEnd_7133887 < baseStart_7133887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133901 : List Nat := [1, 6, 2, 1, 3, 1, 1, 2, 6]
def baseStart_7133901 : Nat := 118140960795 + 7133901 * 2 ^ 59
def prefixEnd_7133901 : Nat := 4983230072969 + 3 ^ 40 * 7133901 * 2
def baseEnd_7133901 : Nat := 407013350510044257025477

theorem tailTrace_7133901 : CollatzResearch.WordTrace tailWord_7133901 prefixEnd_7133901 407013350510044257025477 := by
  unfold tailWord_7133901
  simp only [CollatzResearch.WordTrace]
  refine ⟨260194745328102525136257557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173463163552068350090838371 260194745328102525136257557)
  ·
    refine ⟨12196628687254805865762073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 260194745328102525136257557 12196628687254805865762073)
    ·
      refine ⟨9147471515441104399321555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12196628687254805865762073 9147471515441104399321555)
      ·
        refine ⟨13721207273161656598982333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9147471515441104399321555 13721207273161656598982333)
        ·
          refine ⟨5145452727435621224618375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13721207273161656598982333 5145452727435621224618375)
          ·
            refine ⟨7718179091153431836927563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5145452727435621224618375 7718179091153431836927563)
            ·
              refine ⟨11577268636730147755391345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7718179091153431836927563 11577268636730147755391345)
              ·
                refine ⟨8682951477547610816543509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11577268636730147755391345 8682951477547610816543509)
                ·
                  refine ⟨407013350510044257025477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8682951477547610816543509 407013350510044257025477)
                  ·
                    rfl

theorem cell23_7133901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_7133901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133901 prefixEnd_7133901 := by exact prefixLift 7133901
  have htrace : WordTrace (prefixWord ++ tailWord_7133901) baseStart_7133901 baseEnd_7133901 := by
    simpa [prefixWord, tailWord_7133901, baseEnd_7133901] using wordTrace_append hprefix tailTrace_7133901
  have hstable : (prefixWord ++ tailWord_7133901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133901).length < 2 ^ (prefixWord ++ tailWord_7133901).sum := by decide
  have hdescent : baseEnd_7133901 < baseStart_7133901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133913 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 1, 1, 6]
def baseStart_7133913 : Nat := 118140960795 + 7133913 * 2 ^ 59
def prefixEnd_7133913 : Nat := 4983230072969 + 3 ^ 40 * 7133913 * 2
def baseEnd_7133913 : Nat := 3663126316358252266279237

theorem tailTrace_7133913 : CollatzResearch.WordTrace tailWord_7133913 prefixEnd_7133913 3663126316358252266279237 := by
  unfold tailWord_7133913
  simp only [CollatzResearch.WordTrace]
  refine ⟨260195183004059051185694393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173463455336039367457129595 260195183004059051185694393)
  ·
    refine ⟨195146387253044288389270795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260195183004059051185694393 195146387253044288389270795)
    ·
      refine ⟨292719580879566432583906193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195146387253044288389270795 292719580879566432583906193)
      ·
        refine ⟨219539685659674824437929645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292719580879566432583906193 219539685659674824437929645)
        ·
          refine ⟨82327382122378059164223617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219539685659674824437929645 82327382122378059164223617)
          ·
            refine ⟨61745536591783544373167713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82327382122378059164223617 61745536591783544373167713)
            ·
              refine ⟨46309152443837658279875785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61745536591783544373167713 46309152443837658279875785)
              ·
                refine ⟨34731864332878243709906839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46309152443837658279875785 34731864332878243709906839)
                ·
                  refine ⟨52097796499317365564860259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34731864332878243709906839 52097796499317365564860259)
                  ·
                    refine ⟨78146694748976048347290389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52097796499317365564860259 78146694748976048347290389)
                    ·
                      refine ⟨3663126316358252266279237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78146694748976048347290389 3663126316358252266279237)
                      ·
                        rfl

theorem cell23_7133913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_7133913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133913 prefixEnd_7133913 := by exact prefixLift 7133913
  have htrace : WordTrace (prefixWord ++ tailWord_7133913) baseStart_7133913 baseEnd_7133913 := by
    simpa [prefixWord, tailWord_7133913, baseEnd_7133913] using wordTrace_append hprefix tailTrace_7133913
  have hstable : (prefixWord ++ tailWord_7133913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133913).length < 2 ^ (prefixWord ++ tailWord_7133913).sum := by decide
  have hdescent : baseEnd_7133913 < baseStart_7133913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133934 : List Nat := [4, 1, 2, 1, 1, 3, 2, 2, 3, 2, 2]
def baseStart_7133934 : Nat := 118140960795 + 7133934 * 2 ^ 59
def prefixEnd_7133934 : Nat := 4983230072969 + 3 ^ 40 * 7133934 * 2
def baseEnd_7133934 : Nat := 3663137099451996684116641

theorem tailTrace_7133934 : CollatzResearch.WordTrace tailWord_7133934 prefixEnd_7133934 3663137099451996684116641 := by
  unfold tailWord_7133934
  simp only [CollatzResearch.WordTrace]
  refine ⟨32524493617122871471526107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173463965957988647848139237 32524493617122871471526107)
  ·
    refine ⟨48786740425684307207289161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32524493617122871471526107 48786740425684307207289161)
    ·
      refine ⟨36590055319263230405466871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48786740425684307207289161 36590055319263230405466871)
      ·
        refine ⟨54885082978894845608200307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36590055319263230405466871 54885082978894845608200307)
        ·
          refine ⟨82327624468342268412300461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54885082978894845608200307 82327624468342268412300461)
          ·
            refine ⟨30872859175628350654612673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82327624468342268412300461 30872859175628350654612673)
            ·
              refine ⟨23154644381721262990959505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30872859175628350654612673 23154644381721262990959505)
              ·
                refine ⟨17365983286290947243219629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23154644381721262990959505 17365983286290947243219629)
                ·
                  refine ⟨6512243732359105216207361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17365983286290947243219629 6512243732359105216207361)
                  ·
                    refine ⟨4884182799269328912155521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6512243732359105216207361 4884182799269328912155521)
                    ·
                      refine ⟨3663137099451996684116641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4884182799269328912155521 3663137099451996684116641)
                      ·
                        rfl

theorem cell23_7133934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_7133934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133934 prefixEnd_7133934 := by exact prefixLift 7133934
  have htrace : WordTrace (prefixWord ++ tailWord_7133934) baseStart_7133934 baseEnd_7133934 := by
    simpa [prefixWord, tailWord_7133934, baseEnd_7133934] using wordTrace_append hprefix tailTrace_7133934
  have hstable : (prefixWord ++ tailWord_7133934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133934).length < 2 ^ (prefixWord ++ tailWord_7133934).sum := by decide
  have hdescent : baseEnd_7133934 < baseStart_7133934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133937 : List Nat := [1, 2, 2, 2, 2, 2, 4, 2, 1, 2, 3]
def baseStart_7133937 : Nat := 118140960795 + 7133937 * 2 ^ 59
def prefixEnd_7133937 : Nat := 4983230072969 + 3 ^ 40 * 7133937 * 2
def baseEnd_7133937 : Nat := 3663138639893960172379127

theorem tailTrace_7133937 : CollatzResearch.WordTrace tailWord_7133937 prefixEnd_7133937 3663138639893960172379127 := by
  unfold tailWord_7133937
  simp only [CollatzResearch.WordTrace]
  refine ⟨260196058355972103284568065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173464038903981402189712043 260196058355972103284568065)
  ·
    refine ⟨195147043766979077463426049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260196058355972103284568065 195147043766979077463426049)
    ·
      refine ⟨146360282825234308097569537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195147043766979077463426049 146360282825234308097569537)
      ·
        refine ⟨109770212118925731073177153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146360282825234308097569537 109770212118925731073177153)
        ·
          refine ⟨82327659089194298304882865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109770212118925731073177153 82327659089194298304882865)
          ·
            refine ⟨61745744316895723728662149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82327659089194298304882865 61745744316895723728662149)
            ·
              refine ⟨11577327059417948199124153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61745744316895723728662149 11577327059417948199124153)
              ·
                refine ⟨8682995294563461149343115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11577327059417948199124153 8682995294563461149343115)
                ·
                  refine ⟨13024492941845191724014673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8682995294563461149343115 13024492941845191724014673)
                  ·
                    refine ⟨9768369706383893793011005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13024492941845191724014673 9768369706383893793011005)
                    ·
                      refine ⟨3663138639893960172379127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9768369706383893793011005 3663138639893960172379127)
                      ·
                        rfl

theorem cell23_7133937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_7133937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133937 prefixEnd_7133937 := by exact prefixLift 7133937
  have htrace : WordTrace (prefixWord ++ tailWord_7133937) baseStart_7133937 baseEnd_7133937 := by
    simpa [prefixWord, tailWord_7133937, baseEnd_7133937] using wordTrace_append hprefix tailTrace_7133937
  have hstable : (prefixWord ++ tailWord_7133937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133937).length < 2 ^ (prefixWord ++ tailWord_7133937).sum := by decide
  have hdescent : baseEnd_7133937 < baseStart_7133937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133953 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 1, 9]
def baseStart_7133953 : Nat := 118140960795 + 7133953 * 2 ^ 59
def prefixEnd_7133953 : Nat := 4983230072969 + 3 ^ 40 * 7133953 * 2
def baseEnd_7133953 : Nat := 1221048951861477369926351

theorem tailTrace_7133953 : CollatzResearch.WordTrace tailWord_7133953 prefixEnd_7133953 1221048951861477369926351 := by
  unfold tailWord_7133953
  simp only [CollatzResearch.WordTrace]
  refine ⟨260196641923914138017150513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173464427949276092011433675 260196641923914138017150513)
  ·
    refine ⟨195147481442935603512862885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260196641923914138017150513 195147481442935603512862885)
    ·
      refine ⟨36590152770550425658661791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195147481442935603512862885 36590152770550425658661791)
      ·
        refine ⟨54885229155825638487992687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36590152770550425658661791 54885229155825638487992687)
        ·
          refine ⟨82327843733738457731989031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54885229155825638487992687 82327843733738457731989031)
          ·
            refine ⟨123491765600607686597983547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82327843733738457731989031 123491765600607686597983547)
            ·
              refine ⟨185237648400911529896975321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123491765600607686597983547 185237648400911529896975321)
              ·
                refine ⟨138928236300683647422731491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185237648400911529896975321 138928236300683647422731491)
                ·
                  refine ⟨208392354451025471134097237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138928236300683647422731491 208392354451025471134097237)
                  ·
                    refine ⟨1221048951861477369926351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 208392354451025471134097237 1221048951861477369926351)
                    ·
                      rfl

theorem cell23_7133953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_7133953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133953 prefixEnd_7133953 := by exact prefixLift 7133953
  have htrace : WordTrace (prefixWord ++ tailWord_7133953) baseStart_7133953 baseEnd_7133953 := by
    simpa [prefixWord, tailWord_7133953, baseEnd_7133953] using wordTrace_append hprefix tailTrace_7133953
  have hstable : (prefixWord ++ tailWord_7133953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133953).length < 2 ^ (prefixWord ++ tailWord_7133953).sum := by decide
  have hdescent : baseEnd_7133953 < baseStart_7133953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133954 : List Nat := [3, 4, 1, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_7133954 : Nat := 118140960795 + 7133954 * 2 ^ 59
def prefixEnd_7133954 : Nat := 4983230072969 + 3 ^ 40 * 7133954 * 2
def baseEnd_7133954 : Nat := 3663147369065086605866549

theorem tailTrace_7133954 : CollatzResearch.WordTrace tailWord_7133954 prefixEnd_7133954 3663147369065086605866549 := by
  unfold tailWord_7133954
  simp only [CollatzResearch.WordTrace]
  refine ⟨65049169599227628796984229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173464452264607010125291277 65049169599227628796984229)
  ·
    refine ⟨12196719299855180399434543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65049169599227628796984229 12196719299855180399434543)
    ·
      refine ⟨18295078949782770599151815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12196719299855180399434543 18295078949782770599151815)
      ·
        refine ⟨27442618424674155898727723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18295078949782770599151815 27442618424674155898727723)
        ·
          refine ⟨41163927637011233848091585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27442618424674155898727723 41163927637011233848091585)
          ·
            refine ⟨30872945727758425386068689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41163927637011233848091585 30872945727758425386068689)
            ·
              refine ⟨23154709295818819039551517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30872945727758425386068689 23154709295818819039551517)
              ·
                refine ⟨8683015985932057139831819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23154709295818819039551517 8683015985932057139831819)
                ·
                  refine ⟨13024523978898085709747729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8683015985932057139831819 13024523978898085709747729)
                  ·
                    refine ⟨9768392984173564282310797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13024523978898085709747729 9768392984173564282310797)
                    ·
                      refine ⟨3663147369065086605866549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9768392984173564282310797 3663147369065086605866549)
                      ·
                        rfl

theorem cell23_7133954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_7133954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133954 prefixEnd_7133954 := by exact prefixLift 7133954
  have htrace : WordTrace (prefixWord ++ tailWord_7133954) baseStart_7133954 baseEnd_7133954 := by
    simpa [prefixWord, tailWord_7133954, baseEnd_7133954] using wordTrace_append hprefix tailTrace_7133954
  have hstable : (prefixWord ++ tailWord_7133954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133954).length < 2 ^ (prefixWord ++ tailWord_7133954).sum := by decide
  have hdescent : baseEnd_7133954 < baseStart_7133954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133963 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 5]
def baseStart_7133963 : Nat := 118140960795 + 7133963 * 2 ^ 59
def prefixEnd_7133963 : Nat := 4983230072969 + 3 ^ 40 * 7133963 * 2
def baseEnd_7133963 : Nat := 3663151990390977070654007

theorem tailTrace_7133963 : CollatzResearch.WordTrace tailWord_7133963 prefixEnd_7133963 3663151990390977070654007 := by
  unfold tailWord_7133963
  simp only [CollatzResearch.WordTrace]
  refine ⟨260197006653877909725014543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173464671102585273150009695 260197006653877909725014543)
  ·
    refine ⟨390295509980816864587521815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260197006653877909725014543 390295509980816864587521815)
    ·
      refine ⟨585443264971225296881282723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390295509980816864587521815 585443264971225296881282723)
      ·
        refine ⟨878164897456837945321924085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585443264971225296881282723 878164897456837945321924085)
        ·
          refine ⟨82327959136578557373930383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 878164897456837945321924085 82327959136578557373930383)
          ·
            refine ⟨123491938704867836060895575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82327959136578557373930383 123491938704867836060895575)
            ·
              refine ⟨185237908057301754091343363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123491938704867836060895575 185237908057301754091343363)
              ·
                refine ⟨277856862085952631137015045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185237908057301754091343363 277856862085952631137015045)
                ·
                  refine ⟨52098161641116118338190321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 277856862085952631137015045 52098161641116118338190321)
                  ·
                    refine ⟨39073621230837088753642741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52098161641116118338190321 39073621230837088753642741)
                    ·
                      refine ⟨3663151990390977070654007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39073621230837088753642741 3663151990390977070654007)
                      ·
                        rfl

theorem cell23_7133963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 5].length) (baseStart_7133963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133963 prefixEnd_7133963 := by exact prefixLift 7133963
  have htrace : WordTrace (prefixWord ++ tailWord_7133963) baseStart_7133963 baseEnd_7133963 := by
    simpa [prefixWord, tailWord_7133963, baseEnd_7133963] using wordTrace_append hprefix tailTrace_7133963
  have hstable : (prefixWord ++ tailWord_7133963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133963).length < 2 ^ (prefixWord ++ tailWord_7133963).sum := by decide
  have hdescent : baseEnd_7133963 < baseStart_7133963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133967 : List Nat := [1, 1, 2, 1, 1, 1, 6, 4, 2, 1, 3]
def baseStart_7133967 : Nat := 118140960795 + 7133967 * 2 ^ 59
def prefixEnd_7133967 : Nat := 4983230072969 + 3 ^ 40 * 7133967 * 2
def baseEnd_7133967 : Nat := 3663154044313595055003989

theorem tailTrace_7133967 : CollatzResearch.WordTrace tailWord_7133967 prefixEnd_7133967 3663154044313595055003989 := by
  unfold tailWord_7133967
  simp only [CollatzResearch.WordTrace]
  refine ⟨260197152545863418408160155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173464768363908945605440103 260197152545863418408160155)
  ·
    refine ⟨390295728818795127612240233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260197152545863418408160155 390295728818795127612240233)
    ·
      refine ⟨292721796614096345709180175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390295728818795127612240233 292721796614096345709180175)
      ·
        refine ⟨439082694921144518563770263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292721796614096345709180175 439082694921144518563770263)
        ·
          refine ⟨658624042381716777845655395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439082694921144518563770263 658624042381716777845655395)
          ·
            refine ⟨987936063572575166768483093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658624042381716777845655395 987936063572575166768483093)
            ·
              refine ⟨46309502979964460942272645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 987936063572575166768483093 46309502979964460942272645)
              ·
                refine ⟨8683031808743336426676121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46309502979964460942272645 8683031808743336426676121)
                ·
                  refine ⟨6512273856557502320007091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8683031808743336426676121 6512273856557502320007091)
                  ·
                    refine ⟨9768410784836253480010637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6512273856557502320007091 9768410784836253480010637)
                    ·
                      refine ⟨3663154044313595055003989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9768410784836253480010637 3663154044313595055003989)
                      ·
                        rfl

theorem cell23_7133967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 1, 3].length) (baseStart_7133967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133967 prefixEnd_7133967 := by exact prefixLift 7133967
  have htrace : WordTrace (prefixWord ++ tailWord_7133967) baseStart_7133967 baseEnd_7133967 := by
    simpa [prefixWord, tailWord_7133967, baseEnd_7133967] using wordTrace_append hprefix tailTrace_7133967
  have hstable : (prefixWord ++ tailWord_7133967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133967).length < 2 ^ (prefixWord ++ tailWord_7133967).sum := by decide
  have hdescent : baseEnd_7133967 < baseStart_7133967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133984 : List Nat := [2, 1, 1, 5, 1, 3, 1, 3, 2, 1, 3]
def baseStart_7133984 : Nat := 118140960795 + 7133984 * 2 ^ 59
def prefixEnd_7133984 : Nat := 4983230072969 + 3 ^ 40 * 7133984 * 2
def baseEnd_7133984 : Nat := 3663162773484721488491411

theorem tailTrace_7133984 : CollatzResearch.WordTrace tailWord_7133984 prefixEnd_7133984 3663162773484721488491411 := by
  unfold tailWord_7133984
  simp only [CollatzResearch.WordTrace]
  refine ⟨130098886293400915155764503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173465181724534553541019337 130098886293400915155764503)
  ·
    refine ⟨195148329440101372733646755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130098886293400915155764503 195148329440101372733646755)
    ·
      refine ⟨292722494160152059100470133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195148329440101372733646755 292722494160152059100470133)
      ·
        refine ⟨27442733827514255540669075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 292722494160152059100470133 27442733827514255540669075)
        ·
          refine ⟨41164100741271383311003613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27442733827514255540669075 41164100741271383311003613)
          ·
            refine ⟨15436537777976768741626355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41164100741271383311003613 15436537777976768741626355)
            ·
              refine ⟨23154806666965153112439533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15436537777976768741626355 23154806666965153112439533)
              ·
                refine ⟨8683052500111932417164825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23154806666965153112439533 8683052500111932417164825)
                ·
                  refine ⟨6512289375083949312873619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8683052500111932417164825 6512289375083949312873619)
                  ·
                    refine ⟨9768434062625923969310429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6512289375083949312873619 9768434062625923969310429)
                    ·
                      refine ⟨3663162773484721488491411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9768434062625923969310429 3663162773484721488491411)
                      ·
                        rfl

theorem cell23_7133984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_7133984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133984 prefixEnd_7133984 := by exact prefixLift 7133984
  have htrace : WordTrace (prefixWord ++ tailWord_7133984) baseStart_7133984 baseEnd_7133984 := by
    simpa [prefixWord, tailWord_7133984, baseEnd_7133984] using wordTrace_append hprefix tailTrace_7133984
  have hstable : (prefixWord ++ tailWord_7133984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133984).length < 2 ^ (prefixWord ++ tailWord_7133984).sum := by decide
  have hdescent : baseEnd_7133984 < baseStart_7133984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7133993 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 3, 3, 5]
def baseStart_7133993 : Nat := 118140960795 + 7133993 * 2 ^ 59
def prefixEnd_7133993 : Nat := 4983230072969 + 3 ^ 40 * 7133993 * 2
def baseEnd_7133993 : Nat := 3663167394810611953278869

theorem tailTrace_7133993 : CollatzResearch.WordTrace tailWord_7133993 prefixEnd_7133993 3663167394810611953278869 := by
  unfold tailWord_7133993
  simp only [CollatzResearch.WordTrace]
  refine ⟨260198100843769224848606633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173465400562512816565737755 260198100843769224848606633)
  ·
    refine ⟨195148575632826918636454975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260198100843769224848606633 195148575632826918636454975)
    ·
      refine ⟨292722863449240377954682463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195148575632826918636454975 292722863449240377954682463)
      ·
        refine ⟨439084295173860566932023695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292722863449240377954682463 439084295173860566932023695)
        ·
          refine ⟨658626442760790850398035543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439084295173860566932023695 658626442760790850398035543)
          ·
            refine ⟨987939664141186275597053315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658626442760790850398035543 987939664141186275597053315)
            ·
              refine ⟨1481909496211779413395579973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987939664141186275597053315 1481909496211779413395579973)
              ·
                refine ⟨277858030539708640011671245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1481909496211779413395579973 277858030539708640011671245)
                ·
                  refine ⟨104196761452390740004376717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277858030539708640011671245 104196761452390740004376717)
                  ·
                    refine ⟨39073785544646527501641269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104196761452390740004376717 39073785544646527501641269)
                    ·
                      refine ⟨3663167394810611953278869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39073785544646527501641269 3663167394810611953278869)
                      ·
                        rfl

theorem cell23_7133993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_7133993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7133993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7133993 prefixEnd_7133993 := by exact prefixLift 7133993
  have htrace : WordTrace (prefixWord ++ tailWord_7133993) baseStart_7133993 baseEnd_7133993 := by
    simpa [prefixWord, tailWord_7133993, baseEnd_7133993] using wordTrace_append hprefix tailTrace_7133993
  have hstable : (prefixWord ++ tailWord_7133993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7133993).length < 2 ^ (prefixWord ++ tailWord_7133993).sum := by decide
  have hdescent : baseEnd_7133993 < baseStart_7133993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7133993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134007 : List Nat := [1, 1, 3, 1, 2, 1, 5, 2, 1, 4, 2]
def baseStart_7134007 : Nat := 118140960795 + 7134007 * 2 ^ 59
def prefixEnd_7134007 : Nat := 4983230072969 + 3 ^ 40 * 7134007 * 2
def baseEnd_7134007 : Nat := 3663174583539774898503805

theorem tailTrace_7134007 : CollatzResearch.WordTrace tailWord_7134007 prefixEnd_7134007 3663174583539774898503805 := by
  unfold tailWord_7134007
  simp only [CollatzResearch.WordTrace]
  refine ⟨260198611465718505239616275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173465740977145670159744183 260198611465718505239616275)
  ·
    refine ⟨390297917198577757859424413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260198611465718505239616275 390297917198577757859424413)
    ·
      refine ⟨146361718949466659197284155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390297917198577757859424413 146361718949466659197284155)
      ·
        refine ⟨219542578424199988795926233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146361718949466659197284155 219542578424199988795926233)
        ·
          refine ⟨164656933818149991596944675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219542578424199988795926233 164656933818149991596944675)
          ·
            refine ⟨246985400727224987395417013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164656933818149991596944675 246985400727224987395417013)
            ·
              refine ⟨23154881318177342568320345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 246985400727224987395417013 23154881318177342568320345)
              ·
                refine ⟨17366160988633006926240259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23154881318177342568320345 17366160988633006926240259)
                ·
                  refine ⟨26049241482949510389360389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17366160988633006926240259 26049241482949510389360389)
                  ·
                    refine ⟨4884232778053033198005073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26049241482949510389360389 4884232778053033198005073)
                    ·
                      refine ⟨3663174583539774898503805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4884232778053033198005073 3663174583539774898503805)
                      ·
                        rfl

theorem cell23_7134007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 4, 2].length) (baseStart_7134007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134007 prefixEnd_7134007 := by exact prefixLift 7134007
  have htrace : WordTrace (prefixWord ++ tailWord_7134007) baseStart_7134007 baseEnd_7134007 := by
    simpa [prefixWord, tailWord_7134007, baseEnd_7134007] using wordTrace_append hprefix tailTrace_7134007
  have hstable : (prefixWord ++ tailWord_7134007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134007).length < 2 ^ (prefixWord ++ tailWord_7134007).sum := by decide
  have hdescent : baseEnd_7134007 < baseStart_7134007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134043 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 4, 11]
def baseStart_7134043 : Nat := 118140960795 + 7134043 * 2 ^ 59
def prefixEnd_7134043 : Nat := 4983230072969 + 3 ^ 40 * 7134043 * 2
def baseEnd_7134043 : Nat := 1221064356281112252551213

theorem tailTrace_7134043 : CollatzResearch.WordTrace tailWord_7134043 prefixEnd_7134043 1221064356281112252551213 := by
  unfold tailWord_7134043
  simp only [CollatzResearch.WordTrace]
  refine ⟨260199924493588083387926783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173466616329058722258617855 260199924493588083387926783)
  ·
    refine ⟨390299886740382125081890175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260199924493588083387926783 390299886740382125081890175)
    ·
      refine ⟨585449830110573187622835263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390299886740382125081890175 585449830110573187622835263)
      ·
        refine ⟨878174745165859781434252895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585449830110573187622835263 878174745165859781434252895)
        ·
          refine ⟨1317262117748789672151379343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878174745165859781434252895 1317262117748789672151379343)
          ·
            refine ⟨1975893176623184508227069015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317262117748789672151379343 1975893176623184508227069015)
            ·
              refine ⟨2963839764934776762340603523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1975893176623184508227069015 2963839764934776762340603523)
              ·
                refine ⟨4445759647402165143510905285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2963839764934776762340603523 4445759647402165143510905285)
                ·
                  refine ⟨833579933887905964408294741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4445759647402165143510905285 833579933887905964408294741)
                  ·
                    refine ⟨1221064356281112252551213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 833579933887905964408294741 1221064356281112252551213)
                    ·
                      rfl

theorem cell23_7134043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 11].length) (baseStart_7134043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134043 prefixEnd_7134043 := by exact prefixLift 7134043
  have htrace : WordTrace (prefixWord ++ tailWord_7134043) baseStart_7134043 baseEnd_7134043 := by
    simpa [prefixWord, tailWord_7134043, baseEnd_7134043] using wordTrace_append hprefix tailTrace_7134043
  have hstable : (prefixWord ++ tailWord_7134043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134043).length < 2 ^ (prefixWord ++ tailWord_7134043).sum := by decide
  have hdescent : baseEnd_7134043 < baseStart_7134043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134060 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 1, 7]
def baseStart_7134060 : Nat := 118140960795 + 7134060 * 2 ^ 59
def prefixEnd_7134060 : Nat := 4983230072969 + 3 ^ 40 * 7134060 * 2
def baseEnd_7134060 : Nat := 1221067266004821063713687

theorem tailTrace_7134060 : CollatzResearch.WordTrace tailWord_7134060 prefixEnd_7134060 1221067266004821063713687 := by
  unfold tailWord_7134060
  simp only [CollatzResearch.WordTrace]
  refine ⟨130100272267263247645647817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173467029689684330194197089 130100272267263247645647817)
  ·
    refine ⟨97575204200447435734235863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130100272267263247645647817 97575204200447435734235863)
    ·
      refine ⟨146362806300671153601353795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97575204200447435734235863 146362806300671153601353795)
      ·
        refine ⟨219544209451006730402030693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146362806300671153601353795 219544209451006730402030693)
        ·
          refine ⟨41164539272063761950380755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219544209451006730402030693 41164539272063761950380755)
          ·
            refine ⟨61746808908095642925571133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41164539272063761950380755 61746808908095642925571133)
            ·
              refine ⟨23155053340535866097089175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61746808908095642925571133 23155053340535866097089175)
              ·
                refine ⟨34732580010803799145633763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23155053340535866097089175 34732580010803799145633763)
                ·
                  refine ⟨52098870016205698718450645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34732580010803799145633763 52098870016205698718450645)
                  ·
                    refine ⟨1221067266004821063713687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52098870016205698718450645 1221067266004821063713687)
                    ·
                      rfl

theorem cell23_7134060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_7134060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134060 prefixEnd_7134060 := by exact prefixLift 7134060
  have htrace : WordTrace (prefixWord ++ tailWord_7134060) baseStart_7134060 baseEnd_7134060 := by
    simpa [prefixWord, tailWord_7134060, baseEnd_7134060] using wordTrace_append hprefix tailTrace_7134060
  have hstable : (prefixWord ++ tailWord_7134060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134060).length < 2 ^ (prefixWord ++ tailWord_7134060).sum := by decide
  have hdescent : baseEnd_7134060 < baseStart_7134060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134141 : List Nat := [1, 4, 1, 2, 4, 2, 1, 1, 3, 4]
def baseStart_7134141 : Nat := 118140960795 + 7134141 * 2 ^ 59
def prefixEnd_7134141 : Nat := 4983230072969 + 3 ^ 40 * 7134141 * 2
def baseEnd_7134141 : Nat := 1221081129982492458076063

theorem tailTrace_7134141 : CollatzResearch.WordTrace tailWord_7134141 prefixEnd_7134141 1221081129982492458076063 := by
  unfold tailWord_7134141
  simp only [CollatzResearch.WordTrace]
  refine ⟨260203498847233046124994277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173468999231488697416662851 260203498847233046124994277)
  ·
    refine ⟨48788156033856196148436427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260203498847233046124994277 48788156033856196148436427)
    ·
      refine ⟨73182234050784294222654641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48788156033856196148436427 73182234050784294222654641)
      ·
        refine ⟨54886675538088220666990981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73182234050784294222654641 54886675538088220666990981)
        ·
          refine ⟨10291251663391541375060809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54886675538088220666990981 10291251663391541375060809)
          ·
            refine ⟨7718438747543656031295607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10291251663391541375060809 7718438747543656031295607)
            ·
              refine ⟨11577658121315484046943411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7718438747543656031295607 11577658121315484046943411)
              ·
                refine ⟨17366487181973226070415117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11577658121315484046943411 17366487181973226070415117)
                ·
                  refine ⟨6512432693239959776405669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17366487181973226070415117 6512432693239959776405669)
                  ·
                    refine ⟨1221081129982492458076063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6512432693239959776405669 1221081129982492458076063)
                    ·
                      rfl

theorem cell23_7134141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_7134141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134141 prefixEnd_7134141 := by exact prefixLift 7134141
  have htrace : WordTrace (prefixWord ++ tailWord_7134141) baseStart_7134141 baseEnd_7134141 := by
    simpa [prefixWord, tailWord_7134141, baseEnd_7134141] using wordTrace_append hprefix tailTrace_7134141
  have hstable : (prefixWord ++ tailWord_7134141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134141).length < 2 ^ (prefixWord ++ tailWord_7134141).sum := by decide
  have hdescent : baseEnd_7134141 < baseStart_7134141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134167 : List Nat := [1, 1, 3, 2, 1, 1, 2, 6, 1, 5]
def baseStart_7134167 : Nat := 118140960795 + 7134167 * 2 ^ 59
def prefixEnd_7134167 : Nat := 4983230072969 + 3 ^ 40 * 7134167 * 2
def baseEnd_7134167 : Nat := 1221085580148164757501023

theorem tailTrace_7134167 : CollatzResearch.WordTrace tailWord_7134167 prefixEnd_7134167 1221085580148164757501023 := by
  unfold tailWord_7134167
  simp only [CollatzResearch.WordTrace]
  refine ⟨260204447145138852565440755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173469631430092568376960503 260204447145138852565440755)
  ·
    refine ⟨390306670717708278848161133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260204447145138852565440755 390306670717708278848161133)
    ·
      refine ⟨146365001519140604568060425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390306670717708278848161133 146365001519140604568060425)
      ·
        refine ⟨109773751139355453426045319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146365001519140604568060425 109773751139355453426045319)
        ·
          refine ⟨164660626709033180139067979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109773751139355453426045319 164660626709033180139067979)
          ·
            refine ⟨246990940063549770208601969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164660626709033180139067979 246990940063549770208601969)
            ·
              refine ⟨185243205047662327656451477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246990940063549770208601969 185243205047662327656451477)
              ·
                refine ⟨8683275236609171608896163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 185243205047662327656451477 8683275236609171608896163)
                ·
                  refine ⟨13024912854913757413344245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8683275236609171608896163 13024912854913757413344245)
                  ·
                    refine ⟨1221085580148164757501023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13024912854913757413344245 1221085580148164757501023)
                    ·
                      rfl

theorem cell23_7134167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_7134167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134167 prefixEnd_7134167 := by exact prefixLift 7134167
  have htrace : WordTrace (prefixWord ++ tailWord_7134167) baseStart_7134167 baseEnd_7134167 := by
    simpa [prefixWord, tailWord_7134167, baseEnd_7134167] using wordTrace_append hprefix tailTrace_7134167
  have hstable : (prefixWord ++ tailWord_7134167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134167).length < 2 ^ (prefixWord ++ tailWord_7134167).sum := by decide
  have hdescent : baseEnd_7134167 < baseStart_7134167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134241 : List Nat := [1, 2, 3, 2, 3, 2, 1, 3, 1, 2, 3]
def baseStart_7134241 : Nat := 118140960795 + 7134241 * 2 ^ 59
def prefixEnd_7134241 : Nat := 4983230072969 + 3 ^ 40 * 7134241 * 2
def baseEnd_7134241 : Nat := 3663294738012926982977729

theorem tailTrace_7134241 : CollatzResearch.WordTrace tailWord_7134241 prefixEnd_7134241 3663294738012926982977729 := by
  unfold tailWord_7134241
  simp only [CollatzResearch.WordTrace]
  refine ⟨260207146146870763203634577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173471430764580508802423051 260207146146870763203634577)
  ·
    refine ⟨195155359610153072402725933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260207146146870763203634577 195155359610153072402725933)
    ·
      refine ⟨73183259853807402151022225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195155359610153072402725933 73183259853807402151022225)
      ·
        refine ⟨54887444890355551613266669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73183259853807402151022225 54887444890355551613266669)
        ·
          refine ⟨20582791833883331854975001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54887444890355551613266669 20582791833883331854975001)
          ·
            refine ⟨15437093875412498891231251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20582791833883331854975001 15437093875412498891231251)
            ·
              refine ⟨23155640813118748336846877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15437093875412498891231251 23155640813118748336846877)
              ·
                refine ⟨8683365304919530626317579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23155640813118748336846877 8683365304919530626317579)
                ·
                  refine ⟨13025047957379295939476369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8683365304919530626317579 13025047957379295939476369)
                  ·
                    refine ⟨9768785968034471954607277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13025047957379295939476369 9768785968034471954607277)
                    ·
                      refine ⟨3663294738012926982977729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9768785968034471954607277 3663294738012926982977729)
                      ·
                        rfl

theorem cell23_7134241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_7134241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134241 prefixEnd_7134241 := by exact prefixLift 7134241
  have htrace : WordTrace (prefixWord ++ tailWord_7134241) baseStart_7134241 baseEnd_7134241 := by
    simpa [prefixWord, tailWord_7134241, baseEnd_7134241] using wordTrace_append hprefix tailTrace_7134241
  have hstable : (prefixWord ++ tailWord_7134241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134241).length < 2 ^ (prefixWord ++ tailWord_7134241).sum := by decide
  have hdescent : baseEnd_7134241 < baseStart_7134241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134277 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 2, 3, 4]
def baseStart_7134277 : Nat := 118140960795 + 7134277 * 2 ^ 59
def prefixEnd_7134277 : Nat := 4983230072969 + 3 ^ 40 * 7134277 * 2
def baseEnd_7134277 : Nat := 3663313223316488842127563

theorem tailTrace_7134277 : CollatzResearch.WordTrace tailWord_7134277 prefixEnd_7134277 3663313223316488842127563 := by
  unfold tailWord_7134277
  simp only [CollatzResearch.WordTrace]
  refine ⟨260208459174740341351945085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173472306116493560901296723 260208459174740341351945085)
  ·
    refine ⟨97578172190527628006979407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260208459174740341351945085 97578172190527628006979407)
    ·
      refine ⟨146367258285791442010469111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97578172190527628006979407 146367258285791442010469111)
      ·
        refine ⟨219550887428687163015703667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146367258285791442010469111 219550887428687163015703667)
        ·
          refine ⟨329326331143030744523555501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219550887428687163015703667 329326331143030744523555501)
          ·
            refine ⟨123497374178636529196333313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329326331143030744523555501 123497374178636529196333313)
            ·
              refine ⟨92623030633977396897249985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123497374178636529196333313 92623030633977396897249985)
              ·
                refine ⟨69467272975483047672937489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92623030633977396897249985 69467272975483047672937489)
                ·
                  refine ⟨52100454731612285754703117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69467272975483047672937489 52100454731612285754703117)
                  ·
                    refine ⟨19537670524354607158013669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52100454731612285754703117 19537670524354607158013669)
                    ·
                      refine ⟨3663313223316488842127563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19537670524354607158013669 3663313223316488842127563)
                      ·
                        rfl

theorem cell23_7134277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_7134277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134277 prefixEnd_7134277 := by exact prefixLift 7134277
  have htrace : WordTrace (prefixWord ++ tailWord_7134277) baseStart_7134277 baseEnd_7134277 := by
    simpa [prefixWord, tailWord_7134277, baseEnd_7134277] using wordTrace_append hprefix tailTrace_7134277
  have hstable : (prefixWord ++ tailWord_7134277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134277).length < 2 ^ (prefixWord ++ tailWord_7134277).sum := by decide
  have hdescent : baseEnd_7134277 < baseStart_7134277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134278 : List Nat := [6, 1, 1, 1, 1, 4, 2, 7]
def baseStart_7134278 : Nat := 118140960795 + 7134278 * 2 ^ 59
def prefixEnd_7134278 : Nat := 4983230072969 + 3 ^ 40 * 7134278 * 2
def baseEnd_7134278 : Nat := 135678286548042345859817

theorem tailTrace_7134278 : CollatzResearch.WordTrace tailWord_7134278 prefixEnd_7134278 135678286548042345859817 := by
  unfold tailWord_7134278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8131515488991772453835359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 173472330431824479015154325 8131515488991772453835359)
  ·
    refine ⟨12197273233487658680753039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8131515488991772453835359 12197273233487658680753039)
    ·
      refine ⟨18295909850231488021129559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12197273233487658680753039 18295909850231488021129559)
      ·
        refine ⟨27443864775347232031694339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18295909850231488021129559 27443864775347232031694339)
        ·
          refine ⟨41165797163020848047541509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27443864775347232031694339 41165797163020848047541509)
          ·
            refine ⟨7718586968066409008914033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41165797163020848047541509 7718586968066409008914033)
            ·
              refine ⟨5788940226049806756685525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7718586968066409008914033 5788940226049806756685525)
              ·
                refine ⟨135678286548042345859817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5788940226049806756685525 135678286548042345859817)
                ·
                  rfl

theorem cell23_7134278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_7134278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134278 prefixEnd_7134278 := by exact prefixLift 7134278
  have htrace : WordTrace (prefixWord ++ tailWord_7134278) baseStart_7134278 baseEnd_7134278 := by
    simpa [prefixWord, tailWord_7134278, baseEnd_7134278] using wordTrace_append hprefix tailTrace_7134278
  have hstable : (prefixWord ++ tailWord_7134278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134278).length < 2 ^ (prefixWord ++ tailWord_7134278).sum := by decide
  have hdescent : baseEnd_7134278 < baseStart_7134278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134347 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 1, 7]
def baseStart_7134347 : Nat := 118140960795 + 7134347 * 2 ^ 59
def prefixEnd_7134347 : Nat := 4983230072969 + 3 ^ 40 * 7134347 * 2
def baseEnd_7134347 : Nat := 1221116388987434522750747

theorem tailTrace_7134347 : CollatzResearch.WordTrace tailWord_7134347 prefixEnd_7134347 1221116388987434522750747 := by
  unfold tailWord_7134347
  simp only [CollatzResearch.WordTrace]
  refine ⟨260211012284486743306993295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173474008189657828871328863 260211012284486743306993295)
  ·
    refine ⟨390316518426730114960489943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260211012284486743306993295 390316518426730114960489943)
    ·
      refine ⟨585474777640095172440734915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390316518426730114960489943 585474777640095172440734915)
      ·
        refine ⟨878212166460142758661102373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585474777640095172440734915 878212166460142758661102373)
        ·
          refine ⟨164664781211276767248956695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 878212166460142758661102373 164664781211276767248956695)
          ·
            refine ⟨246997171816915150873435043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164664781211276767248956695 246997171816915150873435043)
            ·
              refine ⟨370495757725372726310152565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246997171816915150873435043 370495757725372726310152565)
              ·
                refine ⟨34733977286753693091576803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 370495757725372726310152565 34733977286753693091576803)
                ·
                  refine ⟨52100965930130539637365205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34733977286753693091576803 52100965930130539637365205)
                  ·
                    refine ⟨1221116388987434522750747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52100965930130539637365205 1221116388987434522750747)
                    ·
                      rfl

theorem cell23_7134347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 7].length) (baseStart_7134347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134347 prefixEnd_7134347 := by exact prefixLift 7134347
  have htrace : WordTrace (prefixWord ++ tailWord_7134347) baseStart_7134347 baseEnd_7134347 := by
    simpa [prefixWord, tailWord_7134347, baseEnd_7134347] using wordTrace_append hprefix tailTrace_7134347
  have hstable : (prefixWord ++ tailWord_7134347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134347).length < 2 ^ (prefixWord ++ tailWord_7134347).sum := by decide
  have hdescent : baseEnd_7134347 < baseStart_7134347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134378 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_7134378 : Nat := 118140960795 + 7134378 * 2 ^ 59
def prefixEnd_7134378 : Nat := 4983230072969 + 3 ^ 40 * 7134378 * 2
def baseEnd_7134378 : Nat := 3663365084862592946964599

theorem tailTrace_7134378 : CollatzResearch.WordTrace tailWord_7134378 prefixEnd_7134378 3663365084862592946964599 := by
  unfold tailWord_7134378
  simp only [CollatzResearch.WordTrace]
  refine ⟨65053035736843608900342947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173474761964916290400914525 65053035736843608900342947)
  ·
    refine ⟨97579553605265413350514421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65053035736843608900342947 97579553605265413350514421)
    ·
      refine ⟨9148083150493632501610727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97579553605265413350514421 9148083150493632501610727)
      ·
        refine ⟨13722124725740448752416091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9148083150493632501610727 13722124725740448752416091)
        ·
          refine ⟨20583187088610673128624137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13722124725740448752416091 20583187088610673128624137)
          ·
            refine ⟨15437390316458004846468103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20583187088610673128624137 15437390316458004846468103)
            ·
              refine ⟨23156085474687007269702155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15437390316458004846468103 23156085474687007269702155)
              ·
                refine ⟨34734128212030510904553233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23156085474687007269702155 34734128212030510904553233)
                ·
                  refine ⟨26050596159022883178414925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34734128212030510904553233 26050596159022883178414925)
                  ·
                    refine ⟨9768973559633581191905597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26050596159022883178414925 9768973559633581191905597)
                    ·
                      refine ⟨3663365084862592946964599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9768973559633581191905597 3663365084862592946964599)
                      ·
                        rfl

theorem cell23_7134378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_7134378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134378 prefixEnd_7134378 := by exact prefixLift 7134378
  have htrace : WordTrace (prefixWord ++ tailWord_7134378) baseStart_7134378 baseEnd_7134378 := by
    simpa [prefixWord, tailWord_7134378, baseEnd_7134378] using wordTrace_append hprefix tailTrace_7134378
  have hstable : (prefixWord ++ tailWord_7134378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134378).length < 2 ^ (prefixWord ++ tailWord_7134378).sum := by decide
  have hdescent : baseEnd_7134378 < baseStart_7134378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134398 : List Nat := [4, 2, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_7134398 : Nat := 118140960795 + 7134398 * 2 ^ 59
def prefixEnd_7134398 : Nat := 4983230072969 + 3 ^ 40 * 7134398 * 2
def baseEnd_7134398 : Nat := 1221125118158560956238169

theorem tailTrace_7134398 : CollatzResearch.WordTrace tailWord_7134398 prefixEnd_7134398 1221125118158560956238169 := by
  unfold tailWord_7134398
  simp only [CollatzResearch.WordTrace]
  refine ⟨32526609050912747377137481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173475248271534652678066565 32526609050912747377137481)
  ·
    refine ⟨24394956788184560532853111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32526609050912747377137481 24394956788184560532853111)
    ·
      refine ⟨36592435182276840799279667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24394956788184560532853111 36592435182276840799279667)
      ·
        refine ⟨54888652773415261198919501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36592435182276840799279667 54888652773415261198919501)
        ·
          refine ⟨20583244790030722949594813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54888652773415261198919501 20583244790030722949594813)
          ·
            refine ⟨7718716796261521106098055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20583244790030722949594813 7718716796261521106098055)
            ·
              refine ⟨11578075194392281659147083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7718716796261521106098055 11578075194392281659147083)
              ·
                refine ⟨17367112791588422488720625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11578075194392281659147083 17367112791588422488720625)
                ·
                  refine ⟨13025334593691316866540469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17367112791588422488720625 13025334593691316866540469)
                  ·
                    refine ⟨1221125118158560956238169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13025334593691316866540469 1221125118158560956238169)
                    ·
                      rfl

theorem cell23_7134398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_7134398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134398 prefixEnd_7134398 := by exact prefixLift 7134398
  have htrace : WordTrace (prefixWord ++ tailWord_7134398) baseStart_7134398 baseEnd_7134398 := by
    simpa [prefixWord, tailWord_7134398, baseEnd_7134398] using wordTrace_append hprefix tailTrace_7134398
  have hstable : (prefixWord ++ tailWord_7134398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134398).length < 2 ^ (prefixWord ++ tailWord_7134398).sum := by decide
  have hdescent : baseEnd_7134398 < baseStart_7134398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134402 : List Nat := [3, 5, 1, 1, 2, 1, 2, 3, 5]
def baseStart_7134402 : Nat := 118140960795 + 7134402 * 2 ^ 59
def prefixEnd_7134402 : Nat := 4983230072969 + 3 ^ 40 * 7134402 * 2
def baseEnd_7134402 : Nat := 407041934266477872562721

theorem tailTrace_7134402 : CollatzResearch.WordTrace tailWord_7134402 prefixEnd_7134402 407041934266477872562721 := by
  unfold tailWord_7134402
  simp only [CollatzResearch.WordTrace]
  refine ⟨65053254574821871925061365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173475345532858325133496973 65053254574821871925061365)
  ·
    refine ⟨6098742616389550492974503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65053254574821871925061365 6098742616389550492974503)
    ·
      refine ⟨9148113924584325739461755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6098742616389550492974503 9148113924584325739461755)
      ·
        refine ⟨13722170886876488609192633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9148113924584325739461755 13722170886876488609192633)
        ·
          refine ⟨10291628165157366456894475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13722170886876488609192633 10291628165157366456894475)
          ·
            refine ⟨15437442247736049685341713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10291628165157366456894475 15437442247736049685341713)
            ·
              refine ⟨11578081685802037264006285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15437442247736049685341713 11578081685802037264006285)
              ·
                refine ⟨4341780632175763974002357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11578081685802037264006285 4341780632175763974002357)
                ·
                  refine ⟨407041934266477872562721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4341780632175763974002357 407041934266477872562721)
                  ·
                    rfl

theorem cell23_7134402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_7134402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134402 prefixEnd_7134402 := by exact prefixLift 7134402
  have htrace : WordTrace (prefixWord ++ tailWord_7134402) baseStart_7134402 baseEnd_7134402 := by
    simpa [prefixWord, tailWord_7134402, baseEnd_7134402] using wordTrace_append hprefix tailTrace_7134402
  have hstable : (prefixWord ++ tailWord_7134402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134402).length < 2 ^ (prefixWord ++ tailWord_7134402).sum := by decide
  have hdescent : baseEnd_7134402 < baseStart_7134402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134462 : List Nat := [4, 2, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_7134462 : Nat := 118140960795 + 7134462 * 2 ^ 59
def prefixEnd_7134462 : Nat := 4983230072969 + 3 ^ 40 * 7134462 * 2
def baseEnd_7134462 : Nat := 1221136072412523539438071

theorem tailTrace_7134462 : CollatzResearch.WordTrace tailWord_7134462 prefixEnd_7134462 1221136072412523539438071 := by
  unfold tailWord_7134462
  simp only [CollatzResearch.WordTrace]
  refine ⟨32526900834883764743428705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173476804452713411964953093 32526900834883764743428705)
  ·
    refine ⟨24395175626162823557571529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32526900834883764743428705 24395175626162823557571529)
    ·
      refine ⟨18296381719622117668178647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24395175626162823557571529 18296381719622117668178647)
      ·
        refine ⟨27444572579433176502267971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18296381719622117668178647 27444572579433176502267971)
        ·
          refine ⟨41166858869149764753401957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27444572579433176502267971 41166858869149764753401957)
          ·
            refine ⟨7718786037965580891262867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41166858869149764753401957 7718786037965580891262867)
            ·
              refine ⟨11578179056948371336894301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7718786037965580891262867 11578179056948371336894301)
              ·
                refine ⟨4341817146355639251335363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11578179056948371336894301 4341817146355639251335363)
                ·
                  refine ⟨6512725719533458877003045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4341817146355639251335363 6512725719533458877003045)
                  ·
                    refine ⟨1221136072412523539438071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6512725719533458877003045 1221136072412523539438071)
                    ·
                      rfl

theorem cell23_7134462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_7134462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134462 prefixEnd_7134462 := by exact prefixLift 7134462
  have htrace : WordTrace (prefixWord ++ tailWord_7134462) baseStart_7134462 baseEnd_7134462 := by
    simpa [prefixWord, tailWord_7134462, baseEnd_7134462] using wordTrace_append hprefix tailTrace_7134462
  have hstable : (prefixWord ++ tailWord_7134462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134462).length < 2 ^ (prefixWord ++ tailWord_7134462).sum := by decide
  have hdescent : baseEnd_7134462 < baseStart_7134462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134478 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2]
def baseStart_7134478 : Nat := 118140960795 + 7134478 * 2 ^ 59
def prefixEnd_7134478 : Nat := 4983230072969 + 3 ^ 40 * 7134478 * 2
def baseEnd_7134478 : Nat := 3663416432928042555714139

theorem tailTrace_7134478 : CollatzResearch.WordTrace tailWord_7134478 prefixEnd_7134478 3663416432928042555714139 := by
  unfold tailWord_7134478
  simp only [CollatzResearch.WordTrace]
  refine ⟨32526973780876519085001511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173477193498008101786674725 32526973780876519085001511)
  ·
    refine ⟨48790460671314778627502267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32526973780876519085001511 48790460671314778627502267)
    ·
      refine ⟨73185691006972167941253401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48790460671314778627502267 73185691006972167941253401)
      ·
        refine ⟨54889268255229125955940051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73185691006972167941253401 54889268255229125955940051)
        ·
          refine ⟨82333902382843688933910077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54889268255229125955940051 82333902382843688933910077)
          ·
            refine ⟨30875213393566383350216279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82333902382843688933910077 30875213393566383350216279)
            ·
              refine ⟨46312820090349575025324419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30875213393566383350216279 46312820090349575025324419)
              ·
                refine ⟨69469230135524362537986629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46312820090349575025324419 69469230135524362537986629)
                ·
                  refine ⟨13025480650410817975872493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69469230135524362537986629 13025480650410817975872493)
                  ·
                    refine ⟨4884555243904056740952185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13025480650410817975872493 4884555243904056740952185)
                    ·
                      refine ⟨3663416432928042555714139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4884555243904056740952185 3663416432928042555714139)
                      ·
                        rfl

theorem cell23_7134478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_7134478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134478 prefixEnd_7134478 := by exact prefixLift 7134478
  have htrace : WordTrace (prefixWord ++ tailWord_7134478) baseStart_7134478 baseEnd_7134478 := by
    simpa [prefixWord, tailWord_7134478, baseEnd_7134478] using wordTrace_append hprefix tailTrace_7134478
  have hstable : (prefixWord ++ tailWord_7134478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134478).length < 2 ^ (prefixWord ++ tailWord_7134478).sum := by decide
  have hdescent : baseEnd_7134478 < baseStart_7134478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134508 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 5, 2, 2]
def baseStart_7134508 : Nat := 118140960795 + 7134508 * 2 ^ 59
def prefixEnd_7134508 : Nat := 4983230072969 + 3 ^ 40 * 7134508 * 2
def baseEnd_7134508 : Nat := 3663431837347677438339001

theorem tailTrace_7134508 : CollatzResearch.WordTrace tailWord_7134508 prefixEnd_7134508 3663431837347677438339001 := by
  unfold tailWord_7134508
  simp only [CollatzResearch.WordTrace]
  refine ⟨130108442218451733901802089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173477922957935645202402785 130108442218451733901802089)
  ·
    refine ⟨97581331663838800426351567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130108442218451733901802089 97581331663838800426351567)
    ·
      refine ⟨146371997495758200639527351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97581331663838800426351567 146371997495758200639527351)
      ·
        refine ⟨219557996243637300959291027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146371997495758200639527351 219557996243637300959291027)
        ·
          refine ⟨329336994365455951438936541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219557996243637300959291027 329336994365455951438936541)
          ·
            refine ⟨123501372887045981789601203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329336994365455951438936541 123501372887045981789601203)
            ·
              refine ⟨185252059330568972684401805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123501372887045981789601203 185252059330568972684401805)
              ·
                refine ⟨69469522248963364756650677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185252059330568972684401805 69469522248963364756650677)
                ·
                  refine ⟨6512767710840315445936001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69469522248963364756650677 6512767710840315445936001)
                  ·
                    refine ⟨4884575783130236584452001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6512767710840315445936001 4884575783130236584452001)
                    ·
                      refine ⟨3663431837347677438339001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4884575783130236584452001 3663431837347677438339001)
                      ·
                        rfl

theorem cell23_7134508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 2, 2].length) (baseStart_7134508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134508 prefixEnd_7134508 := by exact prefixLift 7134508
  have htrace : WordTrace (prefixWord ++ tailWord_7134508) baseStart_7134508 baseEnd_7134508 := by
    simpa [prefixWord, tailWord_7134508, baseEnd_7134508] using wordTrace_append hprefix tailTrace_7134508
  have hstable : (prefixWord ++ tailWord_7134508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134508).length < 2 ^ (prefixWord ++ tailWord_7134508).sum := by decide
  have hdescent : baseEnd_7134508 < baseStart_7134508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134542 : List Nat := [4, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2]
def baseStart_7134542 : Nat := 118140960795 + 7134542 * 2 ^ 59
def prefixEnd_7134542 : Nat := 4983230072969 + 3 ^ 40 * 7134542 * 2
def baseEnd_7134542 : Nat := 3663449295689930305313845

theorem tailTrace_7134542 : CollatzResearch.WordTrace tailWord_7134542 prefixEnd_7134542 3663449295689930305313845 := by
  unfold tailWord_7134542
  simp only [CollatzResearch.WordTrace]
  refine ⟨32527265564847536451292735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173478749679186861073561253 32527265564847536451292735)
  ·
    refine ⟨48790898347271304676939103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32527265564847536451292735 48790898347271304676939103)
    ·
      refine ⟨73186347520906957015408655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48790898347271304676939103 73186347520906957015408655)
      ·
        refine ⟨109779521281360435523112983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73186347520906957015408655 109779521281360435523112983)
        ·
          refine ⟨164669281922040653284669475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109779521281360435523112983 164669281922040653284669475)
          ·
            refine ⟨247003922883060979927004213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164669281922040653284669475 247003922883060979927004213)
            ·
              refine ⟨23156617770286966868156645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 247003922883060979927004213 23156617770286966868156645)
              ·
                refine ⟨4341865831928806287779371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23156617770286966868156645 4341865831928806287779371)
                ·
                  refine ⟨6512798747893209431669057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4341865831928806287779371 6512798747893209431669057)
                  ·
                    refine ⟨4884599060919907073751793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6512798747893209431669057 4884599060919907073751793)
                    ·
                      refine ⟨3663449295689930305313845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4884599060919907073751793 3663449295689930305313845)
                      ·
                        rfl

theorem cell23_7134542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_7134542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134542 prefixEnd_7134542 := by exact prefixLift 7134542
  have htrace : WordTrace (prefixWord ++ tailWord_7134542) baseStart_7134542 baseEnd_7134542 := by
    simpa [prefixWord, tailWord_7134542, baseEnd_7134542] using wordTrace_append hprefix tailTrace_7134542
  have hstable : (prefixWord ++ tailWord_7134542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134542).length < 2 ^ (prefixWord ++ tailWord_7134542).sum := by decide
  have hdescent : baseEnd_7134542 < baseStart_7134542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134544 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 1, 9]
def baseStart_7134544 : Nat := 118140960795 + 7134544 * 2 ^ 59
def prefixEnd_7134544 : Nat := 4983230072969 + 3 ^ 40 * 7134544 * 2
def baseEnd_7134544 : Nat := 1221150107550413099162945

theorem tailTrace_7134544 : CollatzResearch.WordTrace tailWord_7134544 prefixEnd_7134544 1221150107550413099162945 := by
  unfold tailWord_7134544
  simp only [CollatzResearch.WordTrace]
  refine ⟨130109098732386522975957343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173478798309848697301276457 130109098732386522975957343)
  ·
    refine ⟨195163648098579784463936015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130109098732386522975957343 195163648098579784463936015)
    ·
      refine ⟨292745472147869676695904023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195163648098579784463936015 292745472147869676695904023)
      ·
        refine ⟨439118208221804515043856035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292745472147869676695904023 439118208221804515043856035)
        ·
          refine ⟨658677312332706772565784053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439118208221804515043856035 658677312332706772565784053)
          ·
            refine ⟨61750998031191259928042255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 658677312332706772565784053 61750998031191259928042255)
            ·
              refine ⟨92626497046786889892063383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61750998031191259928042255 92626497046786889892063383)
              ·
                refine ⟨138939745570180334838095075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92626497046786889892063383 138939745570180334838095075)
                ·
                  refine ⟨208409618355270502257142613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138939745570180334838095075 208409618355270502257142613)
                  ·
                    refine ⟨1221150107550413099162945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 208409618355270502257142613 1221150107550413099162945)
                    ·
                      rfl

theorem cell23_7134544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 9].length) (baseStart_7134544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134544 prefixEnd_7134544 := by exact prefixLift 7134544
  have htrace : WordTrace (prefixWord ++ tailWord_7134544) baseStart_7134544 baseEnd_7134544 := by
    simpa [prefixWord, tailWord_7134544, baseEnd_7134544] using wordTrace_append hprefix tailTrace_7134544
  have hstable : (prefixWord ++ tailWord_7134544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134544).length < 2 ^ (prefixWord ++ tailWord_7134544).sum := by decide
  have hdescent : baseEnd_7134544 < baseStart_7134544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134671 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 4]
def baseStart_7134671 : Nat := 118140960795 + 7134671 * 2 ^ 59
def prefixEnd_7134671 : Nat := 4983230072969 + 3 ^ 40 * 7134671 * 2
def baseEnd_7134671 : Nat := 3663515534694360300600751

theorem tailTrace_7134671 : CollatzResearch.WordTrace tailWord_7134671 prefixEnd_7134671 3663515534694360300600751 := by
  unfold tailWord_7134671
  simp only [CollatzResearch.WordTrace]
  refine ⟨260222829535312946641787867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173481886356875297761191911 260222829535312946641787867)
  ·
    refine ⟨390334244302969419962681801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260222829535312946641787867 390334244302969419962681801)
    ·
      refine ⟨292750683227227064972011351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390334244302969419962681801 292750683227227064972011351)
      ·
        refine ⟨439126024840840597458017027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292750683227227064972011351 439126024840840597458017027)
        ·
          refine ⟨658689037261260896187025541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439126024840840597458017027 658689037261260896187025541)
          ·
            refine ⟨123504194486486418035067289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 658689037261260896187025541 123504194486486418035067289)
            ·
              refine ⟨92628145864864813526300467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123504194486486418035067289 92628145864864813526300467)
              ·
                refine ⟨138942218797297220289450701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92628145864864813526300467 138942218797297220289450701)
                ·
                  refine ⟨52103332048986457608544013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138942218797297220289450701 52103332048986457608544013)
                  ·
                    refine ⟨19538749518369921603204005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52103332048986457608544013 19538749518369921603204005)
                    ·
                      refine ⟨3663515534694360300600751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19538749518369921603204005 3663515534694360300600751)
                      ·
                        rfl

theorem cell23_7134671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_7134671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134671 prefixEnd_7134671 := by exact prefixLift 7134671
  have htrace : WordTrace (prefixWord ++ tailWord_7134671) baseStart_7134671 baseEnd_7134671 := by
    simpa [prefixWord, tailWord_7134671, baseEnd_7134671] using wordTrace_append hprefix tailTrace_7134671
  have hstable : (prefixWord ++ tailWord_7134671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134671).length < 2 ^ (prefixWord ++ tailWord_7134671).sum := by decide
  have hdescent : baseEnd_7134671 < baseStart_7134671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134685 : List Nat := [1, 4, 3, 1, 1, 3, 2, 1, 2, 5]
def baseStart_7134685 : Nat := 118140960795 + 7134685 * 2 ^ 59
def prefixEnd_7134685 : Nat := 4983230072969 + 3 ^ 40 * 7134685 * 2
def baseEnd_7134685 : Nat := 1221174241141174415275229

theorem tailTrace_7134685 : CollatzResearch.WordTrace tailWord_7134685 prefixEnd_7134685 1221174241141174415275229 := by
  unfold tailWord_7134685
  simp only [CollatzResearch.WordTrace]
  refine ⟨260223340157262227032797509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173482226771508151355198339 260223340157262227032797509)
  ·
    refine ⟨48791876279486667568649533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260223340157262227032797509 48791876279486667568649533)
    ·
      refine ⟨18296953604807500338243575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48791876279486667568649533 18296953604807500338243575)
      ·
        refine ⟨27445430407211250507365363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18296953604807500338243575 27445430407211250507365363)
        ·
          refine ⟨41168145610816875761048045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27445430407211250507365363 41168145610816875761048045)
          ·
            refine ⟨15438054604056328410393017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41168145610816875761048045 15438054604056328410393017)
            ·
              refine ⟨11578540953042246307794763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15438054604056328410393017 11578540953042246307794763)
              ·
                refine ⟨17367811429563369461692145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11578540953042246307794763 17367811429563369461692145)
                ·
                  refine ⟨13025858572172527096269109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17367811429563369461692145 13025858572172527096269109)
                  ·
                    refine ⟨1221174241141174415275229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13025858572172527096269109 1221174241141174415275229)
                    ·
                      rfl

theorem cell23_7134685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_7134685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134685 prefixEnd_7134685 := by exact prefixLift 7134685
  have htrace : WordTrace (prefixWord ++ tailWord_7134685) baseStart_7134685 baseEnd_7134685 := by
    simpa [prefixWord, tailWord_7134685, baseEnd_7134685] using wordTrace_append hprefix tailTrace_7134685
  have hstable : (prefixWord ++ tailWord_7134685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134685).length < 2 ^ (prefixWord ++ tailWord_7134685).sum := by decide
  have hdescent : baseEnd_7134685 < baseStart_7134685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134688 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 3, 6, 2]
def baseStart_7134688 : Nat := 118140960795 + 7134688 * 2 ^ 59
def prefixEnd_7134688 : Nat := 4983230072969 + 3 ^ 40 * 7134688 * 2
def baseEnd_7134688 : Nat := 3663524263865486734088173

theorem tailTrace_7134688 : CollatzResearch.WordTrace tailWord_7134688 prefixEnd_7134688 3663524263865486734088173 := by
  unfold tailWord_7134688
  simp only [CollatzResearch.WordTrace]
  refine ⟨130111724788125679272578359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173482299717500905696771145 130111724788125679272578359)
  ·
    refine ⟨195167587182188518908867539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130111724788125679272578359 195167587182188518908867539)
    ·
      refine ⟨292751380773282778363301309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195167587182188518908867539 292751380773282778363301309)
      ·
        refine ⟨109781767789981041886237991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292751380773282778363301309 109781767789981041886237991)
        ·
          refine ⟨164672651684971562829356987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109781767789981041886237991 164672651684971562829356987)
          ·
            refine ⟨247008977527457344244035481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164672651684971562829356987 247008977527457344244035481)
            ·
              refine ⟨185256733145593008183026611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247008977527457344244035481 185256733145593008183026611)
              ·
                refine ⟨277885099718389512274539917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185256733145593008183026611 277885099718389512274539917)
                ·
                  refine ⟨104206912394396067102952469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277885099718389512274539917 104206912394396067102952469)
                  ·
                    refine ⟨4884699018487315645450897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104206912394396067102952469 4884699018487315645450897)
                    ·
                      refine ⟨3663524263865486734088173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4884699018487315645450897 3663524263865486734088173)
                      ·
                        rfl

theorem cell23_7134688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_7134688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134688 prefixEnd_7134688 := by exact prefixLift 7134688
  have htrace : WordTrace (prefixWord ++ tailWord_7134688) baseStart_7134688 baseEnd_7134688 := by
    simpa [prefixWord, tailWord_7134688, baseEnd_7134688] using wordTrace_append hprefix tailTrace_7134688
  have hstable : (prefixWord ++ tailWord_7134688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134688).length < 2 ^ (prefixWord ++ tailWord_7134688).sum := by decide
  have hdescent : baseEnd_7134688 < baseStart_7134688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134715 : List Nat := [1, 1, 1, 1, 1, 3, 2, 8, 1, 4]
def baseStart_7134715 : Nat := 118140960795 + 7134715 * 2 ^ 59
def prefixEnd_7134715 : Nat := 4983230072969 + 3 ^ 40 * 7134715 * 2
def baseEnd_7134715 : Nat := 1221179375947719376150183

theorem tailTrace_7134715 : CollatzResearch.WordTrace tailWord_7134715 prefixEnd_7134715 1221179375947719376150183 := by
  unfold tailWord_7134715
  simp only [CollatzResearch.WordTrace]
  refine ⟨260224434347153542156389599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173482956231435694770926399 260224434347153542156389599)
  ·
    refine ⟨390336651520730313234584399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260224434347153542156389599 390336651520730313234584399)
    ·
      refine ⟨585504977281095469851876599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390336651520730313234584399 585504977281095469851876599)
      ·
        refine ⟨878257465921643204777814899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585504977281095469851876599 878257465921643204777814899)
        ·
          refine ⟨1317386198882464807166722349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878257465921643204777814899 1317386198882464807166722349)
          ·
            refine ⟨494019824580924302687520881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1317386198882464807166722349 494019824580924302687520881)
            ·
              refine ⟨370514868435693227015640661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494019824580924302687520881 370514868435693227015640661)
              ·
                refine ⟨4341971114480780004089539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 370514868435693227015640661 4341971114480780004089539)
                ·
                  refine ⟨6512956671721170006134309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4341971114480780004089539 6512956671721170006134309)
                  ·
                    refine ⟨1221179375947719376150183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6512956671721170006134309 1221179375947719376150183)
                    ·
                      rfl

theorem cell23_7134715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 1, 4].length) (baseStart_7134715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134715 prefixEnd_7134715 := by exact prefixLift 7134715
  have htrace : WordTrace (prefixWord ++ tailWord_7134715) baseStart_7134715 baseEnd_7134715 := by
    simpa [prefixWord, tailWord_7134715, baseEnd_7134715] using wordTrace_append hprefix tailTrace_7134715
  have hstable : (prefixWord ++ tailWord_7134715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134715).length < 2 ^ (prefixWord ++ tailWord_7134715).sum := by decide
  have hdescent : baseEnd_7134715 < baseStart_7134715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134722 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_7134722 : Nat := 118140960795 + 7134722 * 2 ^ 59
def prefixEnd_7134722 : Nat := 4983230072969 + 3 ^ 40 * 7134722 * 2
def baseEnd_7134722 : Nat := 3663541722207739601063017

theorem tailTrace_7134722 : CollatzResearch.WordTrace tailWord_7134722 prefixEnd_7134722 3663541722207739601063017 := by
  unfold tailWord_7134722
  simp only [CollatzResearch.WordTrace]
  refine ⟨65056172414532045587973605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173483126438752121567929613 65056172414532045587973605)
  ·
    refine ⟨12198032327724758547745051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65056172414532045587973605 12198032327724758547745051)
    ·
      refine ⟨18297048491587137821617577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12198032327724758547745051 18297048491587137821617577)
      ·
        refine ⟨13722786368690353366213183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18297048491587137821617577 13722786368690353366213183)
        ·
          refine ⟨20584179553035530049319775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13722786368690353366213183 20584179553035530049319775)
          ·
            refine ⟨30876269329553295073979663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20584179553035530049319775 30876269329553295073979663)
            ·
              refine ⟨46314403994329942610969495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30876269329553295073979663 46314403994329942610969495)
              ·
                refine ⟨69471605991494913916454243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46314403994329942610969495 69471605991494913916454243)
                ·
                  refine ⟨104207408987242370874681365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69471605991494913916454243 104207408987242370874681365)
                  ·
                    refine ⟨4884722296276986134750689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104207408987242370874681365 4884722296276986134750689)
                    ·
                      refine ⟨3663541722207739601063017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4884722296276986134750689 3663541722207739601063017)
                      ·
                        rfl

theorem cell23_7134722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_7134722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134722 prefixEnd_7134722 := by exact prefixLift 7134722
  have htrace : WordTrace (prefixWord ++ tailWord_7134722) baseStart_7134722 baseEnd_7134722 := by
    simpa [prefixWord, tailWord_7134722, baseEnd_7134722] using wordTrace_append hprefix tailTrace_7134722
  have hstable : (prefixWord ++ tailWord_7134722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134722).length < 2 ^ (prefixWord ++ tailWord_7134722).sum := by decide
  have hdescent : baseEnd_7134722 < baseStart_7134722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134728 : List Nat := [2, 1, 3, 2, 1, 1, 4, 3, 6]
def baseStart_7134728 : Nat := 118140960795 + 7134728 * 2 ^ 59
def prefixEnd_7134728 : Nat := 4983230072969 + 3 ^ 40 * 7134728 * 2
def baseEnd_7134728 : Nat := 407060533676851841954221

theorem tailTrace_7134728 : CollatzResearch.WordTrace tailWord_7134728 prefixEnd_7134728 407060533676851841954221 := by
  unfold tailWord_7134728
  simp only [CollatzResearch.WordTrace]
  refine ⟨130112454248053222688306419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173483272330737630251075225 130112454248053222688306419)
  ·
    refine ⟨195168681372079834032459629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130112454248053222688306419 195168681372079834032459629)
    ·
      refine ⟨73188255514529937762172361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195168681372079834032459629 73188255514529937762172361)
      ·
        refine ⟨54891191635897453321629271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73188255514529937762172361 54891191635897453321629271)
        ·
          refine ⟨82336787453846179982443907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54891191635897453321629271 82336787453846179982443907)
          ·
            refine ⟨123505181180769269973665861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82336787453846179982443907 123505181180769269973665861)
            ·
              refine ⟨23157221471394238120062349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123505181180769269973665861 23157221471394238120062349)
              ·
                refine ⟨8683958051772839295023381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23157221471394238120062349 8683958051772839295023381)
                ·
                  refine ⟨407060533676851841954221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8683958051772839295023381 407060533676851841954221)
                  ·
                    rfl

theorem cell23_7134728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 6].length) (baseStart_7134728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134728 prefixEnd_7134728 := by exact prefixLift 7134728
  have htrace : WordTrace (prefixWord ++ tailWord_7134728) baseStart_7134728 baseEnd_7134728 := by
    simpa [prefixWord, tailWord_7134728, baseEnd_7134728] using wordTrace_append hprefix tailTrace_7134728
  have hstable : (prefixWord ++ tailWord_7134728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134728).length < 2 ^ (prefixWord ++ tailWord_7134728).sum := by decide
  have hdescent : baseEnd_7134728 < baseStart_7134728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134798 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_7134798 : Nat := 118140960795 + 7134798 * 2 ^ 59
def prefixEnd_7134798 : Nat := 4983230072969 + 3 ^ 40 * 7134798 * 2
def baseEnd_7134798 : Nat := 3663580746737481303712667

theorem tailTrace_7134798 : CollatzResearch.WordTrace tailWord_7134798 prefixEnd_7134798 3663580746737481303712667 := by
  unfold tailWord_7134798
  simp only [CollatzResearch.WordTrace]
  refine ⟨32528432700731605916457631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173484974403901898221107365 32528432700731605916457631)
  ·
    refine ⟨48792649051097408874686447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32528432700731605916457631 48792649051097408874686447)
    ·
      refine ⟨73188973576646113312029671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48792649051097408874686447 73188973576646113312029671)
      ·
        refine ⟨109783460364969169968044507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73188973576646113312029671 109783460364969169968044507)
        ·
          refine ⟨164675190547453754952066761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109783460364969169968044507 164675190547453754952066761)
          ·
            refine ⟨123506392910590316214050071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164675190547453754952066761 123506392910590316214050071)
            ·
              refine ⟨185259589365885474321075107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123506392910590316214050071 185259589365885474321075107)
              ·
                refine ⟨277889384048828211481612661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185259589365885474321075107 277889384048828211481612661)
                ·
                  refine ⟨26052129754577644826401187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 277889384048828211481612661 26052129754577644826401187)
                  ·
                    refine ⟨39078194631866467239601781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26052129754577644826401187 39078194631866467239601781)
                    ·
                      refine ⟨3663580746737481303712667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39078194631866467239601781 3663580746737481303712667)
                      ·
                        rfl

theorem cell23_7134798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_7134798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134798 prefixEnd_7134798 := by exact prefixLift 7134798
  have htrace : WordTrace (prefixWord ++ tailWord_7134798) baseStart_7134798 baseEnd_7134798 := by
    simpa [prefixWord, tailWord_7134798, baseEnd_7134798] using wordTrace_append hprefix tailTrace_7134798
  have hstable : (prefixWord ++ tailWord_7134798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134798).length < 2 ^ (prefixWord ++ tailWord_7134798).sum := by decide
  have hdescent : baseEnd_7134798 < baseStart_7134798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134808 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 3, 2, 4]
def baseStart_7134808 : Nat := 118140960795 + 7134808 * 2 ^ 59
def prefixEnd_7134808 : Nat := 4983230072969 + 3 ^ 40 * 7134808 * 2
def baseEnd_7134808 : Nat := 3663585881544026264587621

theorem tailTrace_7134808 : CollatzResearch.WordTrace tailWord_7134808 prefixEnd_7134808 3663585881544026264587621 := by
  unfold tailWord_7134808
  simp only [CollatzResearch.WordTrace]
  refine ⟨130113913167908309519762539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173485217557211079359683385 130113913167908309519762539)
  ·
    refine ⟨195170869751862464279643809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130113913167908309519762539 195170869751862464279643809)
    ·
      refine ⟨146378152313896848209732857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195170869751862464279643809 146378152313896848209732857)
      ·
        refine ⟨109783614235422636157299643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146378152313896848209732857 109783614235422636157299643)
        ·
          refine ⟨164675421353133954235949465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109783614235422636157299643 164675421353133954235949465)
          ·
            refine ⟨123506566014850465676962099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164675421353133954235949465 123506566014850465676962099)
            ·
              refine ⟨185259849022275698515443149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123506566014850465676962099 185259849022275698515443149)
              ·
                refine ⟨69472443383353386943291181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185259849022275698515443149 69472443383353386943291181)
                ·
                  refine ⟨26052166268757520103734193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69472443383353386943291181 26052166268757520103734193)
                  ·
                    refine ⟨19539124701568140077800645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26052166268757520103734193 19539124701568140077800645)
                    ·
                      refine ⟨3663585881544026264587621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19539124701568140077800645 3663585881544026264587621)
                      ·
                        rfl

theorem cell23_7134808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_7134808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134808 prefixEnd_7134808 := by exact prefixLift 7134808
  have htrace : WordTrace (prefixWord ++ tailWord_7134808) baseStart_7134808 baseEnd_7134808 := by
    simpa [prefixWord, tailWord_7134808, baseEnd_7134808] using wordTrace_append hprefix tailTrace_7134808
  have hstable : (prefixWord ++ tailWord_7134808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134808).length < 2 ^ (prefixWord ++ tailWord_7134808).sum := by decide
  have hdescent : baseEnd_7134808 < baseStart_7134808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134812 : List Nat := [2, 2, 4, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_7134812 : Nat := 118140960795 + 7134812 * 2 ^ 59
def prefixEnd_7134812 : Nat := 4983230072969 + 3 ^ 40 * 7134812 * 2
def baseEnd_7134812 : Nat := 3663587935466644248937603

theorem tailTrace_7134812 : CollatzResearch.WordTrace tailWord_7134812 prefixEnd_7134812 3663587935466644248937603 := by
  unfold tailWord_7134812
  simp only [CollatzResearch.WordTrace]
  refine ⟨130113986113901063861335345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173485314818534751815113793 130113986113901063861335345)
  ·
    refine ⟨97585489585425797896001509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130113986113901063861335345 97585489585425797896001509)
    ·
      refine ⟨18297279297267337105500283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97585489585425797896001509 18297279297267337105500283)
      ·
        refine ⟨27445918945901005658250425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18297279297267337105500283 27445918945901005658250425)
        ·
          refine ⟨20584439209425754243687819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27445918945901005658250425 20584439209425754243687819)
          ·
            refine ⟨30876658814138631365531729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20584439209425754243687819 30876658814138631365531729)
            ·
              refine ⟨23157494110603973524148797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30876658814138631365531729 23157494110603973524148797)
              ·
                refine ⟨8684060291476490071555799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23157494110603973524148797 8684060291476490071555799)
                ·
                  refine ⟨13026090437214735107333699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8684060291476490071555799 13026090437214735107333699)
                  ·
                    refine ⟨19539135655822102661000549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13026090437214735107333699 19539135655822102661000549)
                    ·
                      refine ⟨3663587935466644248937603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19539135655822102661000549 3663587935466644248937603)
                      ·
                        rfl

theorem cell23_7134812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_7134812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134812 prefixEnd_7134812 := by exact prefixLift 7134812
  have htrace : WordTrace (prefixWord ++ tailWord_7134812) baseStart_7134812 baseEnd_7134812 := by
    simpa [prefixWord, tailWord_7134812, baseEnd_7134812] using wordTrace_append hprefix tailTrace_7134812
  have hstable : (prefixWord ++ tailWord_7134812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134812).length < 2 ^ (prefixWord ++ tailWord_7134812).sum := by decide
  have hdescent : baseEnd_7134812 < baseStart_7134812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134849 : List Nat := [1, 2, 4, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_7134849 : Nat := 118140960795 + 7134849 * 2 ^ 59
def prefixEnd_7134849 : Nat := 4983230072969 + 3 ^ 40 * 7134849 * 2
def baseEnd_7134849 : Nat := 3663606934250860604174933

theorem tailTrace_7134849 : CollatzResearch.WordTrace tailWord_7134849 prefixEnd_7134849 3663606934250860604174933 := by
  unfold tailWord_7134849
  simp only [CollatzResearch.WordTrace]
  refine ⟨260229321728668083041767601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173486214485778722027845067 260229321728668083041767601)
  ·
    refine ⟨195171991296501062281325701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260229321728668083041767601 195171991296501062281325701)
    ·
      refine ⟨36594748368093949177748569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195171991296501062281325701 36594748368093949177748569)
      ·
        refine ⟨27446061276070461883311427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36594748368093949177748569 27446061276070461883311427)
        ·
          refine ⟨41169091914105692824967141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27446061276070461883311427 41169091914105692824967141)
          ·
            refine ⟨7719204733894817404681339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41169091914105692824967141 7719204733894817404681339)
            ·
              refine ⟨11578807100842226107022009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7719204733894817404681339 11578807100842226107022009)
              ·
                refine ⟨8684105325631669580266507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11578807100842226107022009 8684105325631669580266507)
                ·
                  refine ⟨13026157988447504370399761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8684105325631669580266507 13026157988447504370399761)
                  ·
                    refine ⟨9769618491335628277799821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13026157988447504370399761 9769618491335628277799821)
                    ·
                      refine ⟨3663606934250860604174933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9769618491335628277799821 3663606934250860604174933)
                      ·
                        rfl

theorem cell23_7134849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_7134849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134849 prefixEnd_7134849 := by exact prefixLift 7134849
  have htrace : WordTrace (prefixWord ++ tailWord_7134849) baseStart_7134849 baseEnd_7134849 := by
    simpa [prefixWord, tailWord_7134849, baseEnd_7134849] using wordTrace_append hprefix tailTrace_7134849
  have hstable : (prefixWord ++ tailWord_7134849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134849).length < 2 ^ (prefixWord ++ tailWord_7134849).sum := by decide
  have hdescent : baseEnd_7134849 < baseStart_7134849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134862 : List Nat := [4, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3]
def baseStart_7134862 : Nat := 118140960795 + 7134862 * 2 ^ 59
def prefixEnd_7134862 : Nat := 4983230072969 + 3 ^ 40 * 7134862 * 2
def baseEnd_7134862 : Nat := 3663613609499369053312373

theorem tailTrace_7134862 : CollatzResearch.WordTrace tailWord_7134862 prefixEnd_7134862 3663613609499369053312373 := by
  unfold tailWord_7134862
  simp only [CollatzResearch.WordTrace]
  refine ⟨32528724484702623282748855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173486530585080657507993893 32528724484702623282748855)
  ·
    refine ⟨48793086727053934924123283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32528724484702623282748855 48793086727053934924123283)
    ·
      refine ⟨73189630090580902386184925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48793086727053934924123283 73189630090580902386184925)
      ·
        refine ⟨27446111283967838394819347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73189630090580902386184925 27446111283967838394819347)
        ·
          refine ⟨41169166925951757592229021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27446111283967838394819347 41169166925951757592229021)
          ·
            refine ⟨15438437597231909097085883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41169166925951757592229021 15438437597231909097085883)
            ·
              refine ⟨23157656395847863645628825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15438437597231909097085883 23157656395847863645628825)
              ·
                refine ⟨17368242296885897734221619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23157656395847863645628825 17368242296885897734221619)
                ·
                  refine ⟨26052363445328846601332429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17368242296885897734221619 26052363445328846601332429)
                  ·
                    refine ⟨9769636291998317475499661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26052363445328846601332429 9769636291998317475499661)
                    ·
                      refine ⟨3663613609499369053312373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9769636291998317475499661 3663613609499369053312373)
                      ·
                        rfl

theorem cell23_7134862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_7134862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134862 prefixEnd_7134862 := by exact prefixLift 7134862
  have htrace : WordTrace (prefixWord ++ tailWord_7134862) baseStart_7134862 baseEnd_7134862 := by
    simpa [prefixWord, tailWord_7134862, baseEnd_7134862] using wordTrace_append hprefix tailTrace_7134862
  have hstable : (prefixWord ++ tailWord_7134862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134862).length < 2 ^ (prefixWord ++ tailWord_7134862).sum := by decide
  have hdescent : baseEnd_7134862 < baseStart_7134862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134866 : List Nat := [3, 2, 3, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_7134866 : Nat := 118140960795 + 7134866 * 2 ^ 59
def prefixEnd_7134866 : Nat := 4983230072969 + 3 ^ 40 * 7134866 * 2
def baseEnd_7134866 : Nat := 3663615663421987037662355

theorem tailTrace_7134866 : CollatzResearch.WordTrace tailWord_7134866 prefixEnd_7134866 3663615663421987037662355 := by
  unfold tailWord_7134866
  simp only [CollatzResearch.WordTrace]
  refine ⟨65057485442401623736284113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173486627846404329963424301 65057485442401623736284113)
  ·
    refine ⟨48793114081801217802213085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65057485442401623736284113 48793114081801217802213085)
    ·
      refine ⟨18297417780675456675829907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48793114081801217802213085 18297417780675456675829907)
      ·
        refine ⟨27446126671013185013744861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18297417780675456675829907 27446126671013185013744861)
        ·
          refine ⟨10292297501629944380154323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27446126671013185013744861 10292297501629944380154323)
          ·
            refine ⟨15438446252444916570231485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10292297501629944380154323 15438446252444916570231485)
            ·
              refine ⟨5789417344666843713836807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15438446252444916570231485 5789417344666843713836807)
              ·
                refine ⟨8684126017000265570755211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5789417344666843713836807 8684126017000265570755211)
                ·
                  refine ⟨13026189025500398356132817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8684126017000265570755211 13026189025500398356132817)
                  ·
                    refine ⟨9769641769125298767099613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13026189025500398356132817 9769641769125298767099613)
                    ·
                      refine ⟨3663615663421987037662355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9769641769125298767099613 3663615663421987037662355)
                      ·
                        rfl

theorem cell23_7134866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_7134866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134866 prefixEnd_7134866 := by exact prefixLift 7134866
  have htrace : WordTrace (prefixWord ++ tailWord_7134866) baseStart_7134866 baseEnd_7134866 := by
    simpa [prefixWord, tailWord_7134866, baseEnd_7134866] using wordTrace_append hprefix tailTrace_7134866
  have hstable : (prefixWord ++ tailWord_7134866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134866).length < 2 ^ (prefixWord ++ tailWord_7134866).sum := by decide
  have hdescent : baseEnd_7134866 < baseStart_7134866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134932 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_7134932 : Nat := 118140960795 + 7134932 * 2 ^ 59
def prefixEnd_7134932 : Nat := 4983230072969 + 3 ^ 40 * 7134932 * 2
def baseEnd_7134932 : Nat := 3663649553145183779437051

theorem tailTrace_7134932 : CollatzResearch.WordTrace tailWord_7134932 prefixEnd_7134932 3663649553145183779437051 := by
  unfold tailWord_7134932
  simp only [CollatzResearch.WordTrace]
  refine ⟨130116174493683694108519525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173488232658244925478026033 130116174493683694108519525)
  ·
    refine ⟨24396782717565692645347411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130116174493683694108519525 24396782717565692645347411)
    ·
      refine ⟨36595174076348538968021117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24396782717565692645347411 36595174076348538968021117)
      ·
        refine ⟨13723190278630702113007919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36595174076348538968021117 13723190278630702113007919)
        ·
          refine ⟨20584785417946053169511879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13723190278630702113007919 20584785417946053169511879)
          ·
            refine ⟨30877178126919079754267819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20584785417946053169511879 30877178126919079754267819)
            ·
              refine ⟨46315767190378619631401729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30877178126919079754267819 46315767190378619631401729)
              ·
                refine ⟨34736825392783964723551297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46315767190378619631401729 34736825392783964723551297)
                ·
                  refine ⟨26052619044587973542663473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34736825392783964723551297 26052619044587973542663473)
                  ·
                    refine ⟨19539464283440980156997605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26052619044587973542663473 19539464283440980156997605)
                    ·
                      refine ⟨3663649553145183779437051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19539464283440980156997605 3663649553145183779437051)
                      ·
                        rfl

theorem cell23_7134932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_7134932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134932 prefixEnd_7134932 := by exact prefixLift 7134932
  have htrace : WordTrace (prefixWord ++ tailWord_7134932) baseStart_7134932 baseEnd_7134932 := by
    simpa [prefixWord, tailWord_7134932, baseEnd_7134932] using wordTrace_append hprefix tailTrace_7134932
  have hstable : (prefixWord ++ tailWord_7134932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134932).length < 2 ^ (prefixWord ++ tailWord_7134932).sum := by decide
  have hdescent : baseEnd_7134932 < baseStart_7134932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134935 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 3]
def baseStart_7134935 : Nat := 118140960795 + 7134935 * 2 ^ 59
def prefixEnd_7134935 : Nat := 4983230072969 + 3 ^ 40 * 7134935 * 2
def baseEnd_7134935 : Nat := 3663651093587147267699537

theorem tailTrace_7134935 : CollatzResearch.WordTrace tailWord_7134935 prefixEnd_7134935 3663651093587147267699537 := by
  unfold tailWord_7134935
  simp only [CollatzResearch.WordTrace]
  refine ⟨260232458406356519729398259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173488305604237679819598839 260232458406356519729398259)
  ·
    refine ⟨390348687609534779594097389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260232458406356519729398259 390348687609534779594097389)
    ·
      refine ⟨146380757853575542347786521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390348687609534779594097389 146380757853575542347786521)
      ·
        refine ⟨109785568390181656760839891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146380757853575542347786521 109785568390181656760839891)
        ·
          refine ⟨164678352585272485141259837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109785568390181656760839891 164678352585272485141259837)
          ·
            refine ⟨61754382219477181927972439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164678352585272485141259837 61754382219477181927972439)
            ·
              refine ⟨92631573329215772891958659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61754382219477181927972439 92631573329215772891958659)
              ·
                refine ⟨138947359993823659337937989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92631573329215772891958659 138947359993823659337937989)
                ·
                  refine ⟨26052629998841936125863373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138947359993823659337937989 26052629998841936125863373)
                  ·
                    refine ⟨9769736249565726047198765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26052629998841936125863373 9769736249565726047198765)
                    ·
                      refine ⟨3663651093587147267699537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9769736249565726047198765 3663651093587147267699537)
                      ·
                        rfl

theorem cell23_7134935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_7134935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134935 prefixEnd_7134935 := by exact prefixLift 7134935
  have htrace : WordTrace (prefixWord ++ tailWord_7134935) baseStart_7134935 baseEnd_7134935 := by
    simpa [prefixWord, tailWord_7134935, baseEnd_7134935] using wordTrace_append hprefix tailTrace_7134935
  have hstable : (prefixWord ++ tailWord_7134935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134935).length < 2 ^ (prefixWord ++ tailWord_7134935).sum := by decide
  have hdescent : baseEnd_7134935 < baseStart_7134935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134952 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_7134952 : Nat := 118140960795 + 7134952 * 2 ^ 59
def prefixEnd_7134952 : Nat := 4983230072969 + 3 ^ 40 * 7134952 * 2
def baseEnd_7134952 : Nat := 3663659822758273701186959

theorem tailTrace_7134952 : CollatzResearch.WordTrace tailWord_7134952 prefixEnd_7134952 3663659822758273701186959 := by
  unfold tailWord_7134952
  simp only [CollatzResearch.WordTrace]
  refine ⟨130116539223647465816383555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173488718964863287755178073 130116539223647465816383555)
  ·
    refine ⟨195174808835471198724575333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130116539223647465816383555 195174808835471198724575333)
    ·
      refine ⟨36595276656650849760857875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195174808835471198724575333 36595276656650849760857875)
      ·
        refine ⟨54892914984976274641286813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36595276656650849760857875 54892914984976274641286813)
        ·
          refine ⟨20584843119366102990482555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54892914984976274641286813 20584843119366102990482555)
          ·
            refine ⟨30877264679049154485723833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20584843119366102990482555 30877264679049154485723833)
            ·
              refine ⟨23157948509286865864292875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30877264679049154485723833 23157948509286865864292875)
              ·
                refine ⟨34736922763930298796439313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23157948509286865864292875 34736922763930298796439313)
                ·
                  refine ⟨26052692072947724097329485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34736922763930298796439313 26052692072947724097329485)
                  ·
                    refine ⟨9769759527355396536498557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26052692072947724097329485 9769759527355396536498557)
                    ·
                      refine ⟨3663659822758273701186959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9769759527355396536498557 3663659822758273701186959)
                      ·
                        rfl

theorem cell23_7134952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_7134952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134952 prefixEnd_7134952 := by exact prefixLift 7134952
  have htrace : WordTrace (prefixWord ++ tailWord_7134952) baseStart_7134952 baseEnd_7134952 := by
    simpa [prefixWord, tailWord_7134952, baseEnd_7134952] using wordTrace_append hprefix tailTrace_7134952
  have hstable : (prefixWord ++ tailWord_7134952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134952).length < 2 ^ (prefixWord ++ tailWord_7134952).sum := by decide
  have hdescent : baseEnd_7134952 < baseStart_7134952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134975 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 4]
def baseStart_7134975 : Nat := 118140960795 + 7134975 * 2 ^ 59
def prefixEnd_7134975 : Nat := 4983230072969 + 3 ^ 40 * 7134975 * 2
def baseEnd_7134975 : Nat := 3663671632813327111199353

theorem tailTrace_7134975 : CollatzResearch.WordTrace tailWord_7134975 prefixEnd_7134975 3663671632813327111199353 := by
  unfold tailWord_7134975
  simp only [CollatzResearch.WordTrace]
  refine ⟨260233917326211606560854379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173489278217474404373902919 260233917326211606560854379)
  ·
    refine ⟨390350875989317409841281569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260233917326211606560854379 390350875989317409841281569)
    ·
      refine ⟨292763156991988057380961177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390350875989317409841281569 292763156991988057380961177)
      ·
        refine ⟨219572367743991043035720883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292763156991988057380961177 219572367743991043035720883)
        ·
          refine ⟨329358551615986564553581325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219572367743991043035720883 329358551615986564553581325)
          ·
            refine ⟨123509456855994961707592997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329358551615986564553581325 123509456855994961707592997)
            ·
              refine ⟨23158023160499055320173687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123509456855994961707592997 23158023160499055320173687)
              ·
                refine ⟨34737034740748582980260531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23158023160499055320173687 34737034740748582980260531)
                ·
                  refine ⟨52105552111122874470390797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34737034740748582980260531 52105552111122874470390797)
                  ·
                    refine ⟨19539582041671077926396549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52105552111122874470390797 19539582041671077926396549)
                    ·
                      refine ⟨3663671632813327111199353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19539582041671077926396549 3663671632813327111199353)
                      ·
                        rfl

theorem cell23_7134975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_7134975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134975 prefixEnd_7134975 := by exact prefixLift 7134975
  have htrace : WordTrace (prefixWord ++ tailWord_7134975) baseStart_7134975 baseEnd_7134975 := by
    simpa [prefixWord, tailWord_7134975, baseEnd_7134975] using wordTrace_append hprefix tailTrace_7134975
  have hstable : (prefixWord ++ tailWord_7134975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134975).length < 2 ^ (prefixWord ++ tailWord_7134975).sum := by decide
  have hdescent : baseEnd_7134975 < baseStart_7134975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7134995 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 3]
def baseStart_7134995 : Nat := 118140960795 + 7134995 * 2 ^ 59
def prefixEnd_7134995 : Nat := 4983230072969 + 3 ^ 40 * 7134995 * 2
def baseEnd_7134995 : Nat := 3663681902426417032949261

theorem tailTrace_7134995 : CollatzResearch.WordTrace tailWord_7134995 prefixEnd_7134995 3663681902426417032949261 := by
  unfold tailWord_7134995
  simp only [CollatzResearch.WordTrace]
  refine ⟨260234646786139149976582439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173489764524092766651054959 260234646786139149976582439)
  ·
    refine ⟨390351970179208724964873659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260234646786139149976582439 390351970179208724964873659)
    ·
      refine ⟨585527955268813087447310489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390351970179208724964873659 585527955268813087447310489)
      ·
        refine ⟨439145966451609815585482867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585527955268813087447310489 439145966451609815585482867)
        ·
          refine ⟨658718949677414723378224301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439145966451609815585482867 658718949677414723378224301)
          ·
            refine ⟨247019606129030521266834113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 658718949677414723378224301 247019606129030521266834113)
            ·
              refine ⟨185264704596772890950125585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247019606129030521266834113 185264704596772890950125585)
              ·
                refine ⟨138948528447579668212594189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185264704596772890950125585 138948528447579668212594189)
                ·
                  refine ⟨52105698167842375579722821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138948528447579668212594189 52105698167842375579722821)
                  ·
                    refine ⟨9769818406470445421198029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52105698167842375579722821 9769818406470445421198029)
                    ·
                      refine ⟨3663681902426417032949261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9769818406470445421198029 3663681902426417032949261)
                      ·
                        rfl

theorem cell23_7134995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 3].length) (baseStart_7134995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7134995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7134995 prefixEnd_7134995 := by exact prefixLift 7134995
  have htrace : WordTrace (prefixWord ++ tailWord_7134995) baseStart_7134995 baseEnd_7134995 := by
    simpa [prefixWord, tailWord_7134995, baseEnd_7134995] using wordTrace_append hprefix tailTrace_7134995
  have hstable : (prefixWord ++ tailWord_7134995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7134995).length < 2 ^ (prefixWord ++ tailWord_7134995).sum := by decide
  have hdescent : baseEnd_7134995 < baseStart_7134995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7134995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135053 : List Nat := [1, 6, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_7135053 : Nat := 118140960795 + 7135053 * 2 ^ 59
def prefixEnd_7135053 : Nat := 4983230072969 + 3 ^ 40 * 7135053 * 2
def baseEnd_7135053 : Nat := 1221237228101459268674665

theorem tailTrace_7135053 : CollatzResearch.WordTrace tailWord_7135053 prefixEnd_7135053 1221237228101459268674665 := by
  unfold tailWord_7135053
  simp only [CollatzResearch.WordTrace]
  refine ⟨260236762219929025882193813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173491174813286017254795875 260236762219929025882193813)
  ·
    refine ⟨12198598229059173088227835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 260236762219929025882193813 12198598229059173088227835)
    ·
      refine ⟨18297897343588759632341753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12198598229059173088227835 18297897343588759632341753)
      ·
        refine ⟨13723423007691569724256315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18297897343588759632341753 13723423007691569724256315)
        ·
          refine ⟨20585134511537354586384473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13723423007691569724256315 20585134511537354586384473)
          ·
            refine ⟨15438850883653015939788355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20585134511537354586384473 15438850883653015939788355)
            ·
              refine ⟨23158276325479523909682533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15438850883653015939788355 23158276325479523909682533)
              ·
                refine ⟨4342176811027410733065475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23158276325479523909682533 4342176811027410733065475)
                ·
                  refine ⟨6513265216541116099598213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4342176811027410733065475 6513265216541116099598213)
                  ·
                    refine ⟨1221237228101459268674665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6513265216541116099598213 1221237228101459268674665)
                    ·
                      rfl

theorem cell23_7135053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_7135053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135053 prefixEnd_7135053 := by exact prefixLift 7135053
  have htrace : WordTrace (prefixWord ++ tailWord_7135053) baseStart_7135053 baseEnd_7135053 := by
    simpa [prefixWord, tailWord_7135053, baseEnd_7135053] using wordTrace_append hprefix tailTrace_7135053
  have hstable : (prefixWord ++ tailWord_7135053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135053).length < 2 ^ (prefixWord ++ tailWord_7135053).sum := by decide
  have hdescent : baseEnd_7135053 < baseStart_7135053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135076 : List Nat := [2, 3, 1, 1, 5, 1, 1, 2, 3, 1, 3]
def baseStart_7135076 : Nat := 118140960795 + 7135076 * 2 ^ 59
def prefixEnd_7135076 : Nat := 4983230072969 + 3 ^ 40 * 7135076 * 2
def baseEnd_7135076 : Nat := 3663723494359431216036389

theorem tailTrace_7135076 : CollatzResearch.WordTrace tailWord_7135076 prefixEnd_7135076 3663723494359431216036389 := by
  unfold tailWord_7135076
  simp only [CollatzResearch.WordTrace]
  refine ⟨130118800549422850405140541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173491734065897133873520721 130118800549422850405140541)
  ·
    refine ⟨48794550206033568901927703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130118800549422850405140541 48794550206033568901927703)
    ·
      refine ⟨73191825309050353352891555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48794550206033568901927703 73191825309050353352891555)
      ·
        refine ⟨109787737963575530029337333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73191825309050353352891555 109787737963575530029337333)
        ·
          refine ⟨10292600434085205940250375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109787737963575530029337333 10292600434085205940250375)
          ·
            refine ⟨15438900651127808910375563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10292600434085205940250375 15438900651127808910375563)
            ·
              refine ⟨23158350976691713365563345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15438900651127808910375563 23158350976691713365563345)
              ·
                refine ⟨17368763232518785024172509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23158350976691713365563345 17368763232518785024172509)
                ·
                  refine ⟨6513286212194544384064691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17368763232518785024172509 6513286212194544384064691)
                  ·
                    refine ⟨9769929318291816576097037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6513286212194544384064691 9769929318291816576097037)
                    ·
                      refine ⟨3663723494359431216036389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9769929318291816576097037 3663723494359431216036389)
                      ·
                        rfl

theorem cell23_7135076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_7135076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135076 prefixEnd_7135076 := by exact prefixLift 7135076
  have htrace : WordTrace (prefixWord ++ tailWord_7135076) baseStart_7135076 baseEnd_7135076 := by
    simpa [prefixWord, tailWord_7135076, baseEnd_7135076] using wordTrace_append hprefix tailTrace_7135076
  have hstable : (prefixWord ++ tailWord_7135076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135076).length < 2 ^ (prefixWord ++ tailWord_7135076).sum := by decide
  have hdescent : baseEnd_7135076 < baseStart_7135076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135086 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 1, 5, 2]
def baseStart_7135086 : Nat := 118140960795 + 7135086 * 2 ^ 59
def prefixEnd_7135086 : Nat := 4983230072969 + 3 ^ 40 * 7135086 * 2
def baseEnd_7135086 : Nat := 3663728629165976176911343

theorem tailTrace_7135086 : CollatzResearch.WordTrace tailWord_7135086 prefixEnd_7135086 3663728629165976176911343 := by
  unfold tailWord_7135086
  simp only [CollatzResearch.WordTrace]
  refine ⟨32529745728601184064768139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173491977219206315012096741 32529745728601184064768139)
  ·
    refine ⟨48794618592901776097152209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32529745728601184064768139 48794618592901776097152209)
    ·
      refine ⟨36595963944676332072864157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48794618592901776097152209 36595963944676332072864157)
      ·
        refine ⟨13723486479253624527324059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36595963944676332072864157 13723486479253624527324059)
        ·
          refine ⟨20585229718880436790986089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13723486479253624527324059 20585229718880436790986089)
          ·
            refine ⟨15438922289160327593239567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20585229718880436790986089 15438922289160327593239567)
            ·
              refine ⟨23158383433740491389859351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15438922289160327593239567 23158383433740491389859351)
              ·
                refine ⟨34737575150610737084789027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23158383433740491389859351 34737575150610737084789027)
                ·
                  refine ⟨52106362725916105627183541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34737575150610737084789027 52106362725916105627183541)
                  ·
                    refine ⟨4884971505554634902548457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52106362725916105627183541 4884971505554634902548457)
                    ·
                      refine ⟨3663728629165976176911343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4884971505554634902548457 3663728629165976176911343)
                      ·
                        rfl

theorem cell23_7135086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_7135086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135086 prefixEnd_7135086 := by exact prefixLift 7135086
  have htrace : WordTrace (prefixWord ++ tailWord_7135086) baseStart_7135086 baseEnd_7135086 := by
    simpa [prefixWord, tailWord_7135086, baseEnd_7135086] using wordTrace_append hprefix tailTrace_7135086
  have hstable : (prefixWord ++ tailWord_7135086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135086).length < 2 ^ (prefixWord ++ tailWord_7135086).sum := by decide
  have hdescent : baseEnd_7135086 < baseStart_7135086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135093 : List Nat := [1, 3, 4, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_7135093 : Nat := 118140960795 + 7135093 * 2 ^ 59
def prefixEnd_7135093 : Nat := 4983230072969 + 3 ^ 40 * 7135093 * 2
def baseEnd_7135093 : Nat := 3663732223530557649523811

theorem tailTrace_7135093 : CollatzResearch.WordTrace tailWord_7135093 prefixEnd_7135093 3663732223530557649523811 := by
  unfold tailWord_7135093
  simp only [CollatzResearch.WordTrace]
  refine ⟨260238221139784112713649933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173492147426522741809099955 260238221139784112713649933)
  ·
    refine ⟨97589332927419042267618725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260238221139784112713649933 97589332927419042267618725)
    ·
      refine ⟨18297999923891070425178511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97589332927419042267618725 18297999923891070425178511)
      ·
        refine ⟨27446999885836605637767767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18297999923891070425178511 27446999885836605637767767)
        ·
          refine ⟨41170499828754908456651651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27446999885836605637767767 41170499828754908456651651)
          ·
            refine ⟨61755749743132362684977477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41170499828754908456651651 61755749743132362684977477)
            ·
              refine ⟨11579203076837318003433277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61755749743132362684977477 11579203076837318003433277)
              ·
                refine ⟨4342201153813994251287479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11579203076837318003433277 4342201153813994251287479)
                ·
                  refine ⟨6513301730720991376931219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4342201153813994251287479 6513301730720991376931219)
                  ·
                    refine ⟨9769952596081487065396829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6513301730720991376931219 9769952596081487065396829)
                    ·
                      refine ⟨3663732223530557649523811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9769952596081487065396829 3663732223530557649523811)
                      ·
                        rfl

theorem cell23_7135093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_7135093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135093 prefixEnd_7135093 := by exact prefixLift 7135093
  have htrace : WordTrace (prefixWord ++ tailWord_7135093) baseStart_7135093 baseEnd_7135093 := by
    simpa [prefixWord, tailWord_7135093, baseEnd_7135093] using wordTrace_append hprefix tailTrace_7135093
  have hstable : (prefixWord ++ tailWord_7135093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135093).length < 2 ^ (prefixWord ++ tailWord_7135093).sum := by decide
  have hdescent : baseEnd_7135093 < baseStart_7135093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135095 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 6]
def baseStart_7135095 : Nat := 118140960795 + 7135095 * 2 ^ 59
def prefixEnd_7135095 : Nat := 4983230072969 + 3 ^ 40 * 7135095 * 2
def baseEnd_7135095 : Nat := 3663733250491866641698801

theorem tailTrace_7135095 : CollatzResearch.WordTrace tailWord_7135095 prefixEnd_7135095 3663733250491866641698801 := by
  unfold tailWord_7135095
  simp only [CollatzResearch.WordTrace]
  refine ⟨260238294085776867055222739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173492196057184578036815159 260238294085776867055222739)
  ·
    refine ⟨390357441128665300582834109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260238294085776867055222739 390357441128665300582834109)
    ·
      refine ⟨146384040423249487718562791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390357441128665300582834109 146384040423249487718562791)
      ·
        refine ⟨219576060634874231577844187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146384040423249487718562791 219576060634874231577844187)
        ·
          refine ⟨329364090952311347366766281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219576060634874231577844187 329364090952311347366766281)
          ·
            refine ⟨247023068214233510525074711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329364090952311347366766281 247023068214233510525074711)
            ·
              refine ⟨370534602321350265787612067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247023068214233510525074711 370534602321350265787612067)
              ·
                refine ⟨555801903482025398681418101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370534602321350265787612067 555801903482025398681418101)
                ·
                  refine ⟨52106428451439881126382947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 555801903482025398681418101 52106428451439881126382947)
                  ·
                    refine ⟨78159642677159821689574421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52106428451439881126382947 78159642677159821689574421)
                    ·
                      refine ⟨3663733250491866641698801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78159642677159821689574421 3663733250491866641698801)
                      ·
                        rfl

theorem cell23_7135095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_7135095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135095 prefixEnd_7135095 := by exact prefixLift 7135095
  have htrace : WordTrace (prefixWord ++ tailWord_7135095) baseStart_7135095 baseEnd_7135095 := by
    simpa [prefixWord, tailWord_7135095, baseEnd_7135095] using wordTrace_append hprefix tailTrace_7135095
  have hstable : (prefixWord ++ tailWord_7135095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135095).length < 2 ^ (prefixWord ++ tailWord_7135095).sum := by decide
  have hdescent : baseEnd_7135095 < baseStart_7135095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135099 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 7, 2, 2]
def baseStart_7135099 : Nat := 118140960795 + 7135099 * 2 ^ 59
def prefixEnd_7135099 : Nat := 4983230072969 + 3 ^ 40 * 7135099 * 2
def baseEnd_7135099 : Nat := 3663735304414484626048783

theorem tailTrace_7135099 : CollatzResearch.WordTrace tailWord_7135099 prefixEnd_7135099 3663735304414484626048783 := by
  unfold tailWord_7135099
  simp only [CollatzResearch.WordTrace]
  refine ⟨260238439977762375738368351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173492293318508250492245567 260238439977762375738368351)
  ·
    refine ⟨390357659966643563607552527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260238439977762375738368351 390357659966643563607552527)
    ·
      refine ⟨585536489949965345411328791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390357659966643563607552527 585536489949965345411328791)
      ·
        refine ⟨878304734924948018116993187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585536489949965345411328791 878304734924948018116993187)
        ·
          refine ⟨1317457102387422027175489781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878304734924948018116993187 1317457102387422027175489781)
          ·
            refine ⟨123511603348820815047702167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1317457102387422027175489781 123511603348820815047702167)
            ·
              refine ⟨185267405023231222571553251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123511603348820815047702167 185267405023231222571553251)
              ·
                refine ⟨277901107534846833857329877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185267405023231222571553251 277901107534846833857329877)
                ·
                  refine ⟨6513307207847972668531169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 277901107534846833857329877 6513307207847972668531169)
                  ·
                    refine ⟨4884980405885979501398377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6513307207847972668531169 4884980405885979501398377)
                    ·
                      refine ⟨3663735304414484626048783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4884980405885979501398377 3663735304414484626048783)
                      ·
                        rfl

theorem cell23_7135099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 2, 2].length) (baseStart_7135099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135099 prefixEnd_7135099 := by exact prefixLift 7135099
  have htrace : WordTrace (prefixWord ++ tailWord_7135099) baseStart_7135099 baseEnd_7135099 := by
    simpa [prefixWord, tailWord_7135099, baseEnd_7135099] using wordTrace_append hprefix tailTrace_7135099
  have hstable : (prefixWord ++ tailWord_7135099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135099).length < 2 ^ (prefixWord ++ tailWord_7135099).sum := by decide
  have hdescent : baseEnd_7135099 < baseStart_7135099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135115 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 7]
def baseStart_7135115 : Nat := 118140960795 + 7135115 * 2 ^ 59
def prefixEnd_7135115 : Nat := 4983230072969 + 3 ^ 40 * 7135115 * 2
def baseEnd_7135115 : Nat := 3663743520104956563448709

theorem tailTrace_7135115 : CollatzResearch.WordTrace tailWord_7135115 prefixEnd_7135115 3663743520104956563448709 := by
  unfold tailWord_7135115
  simp only [CollatzResearch.WordTrace]
  refine ⟨260239023545704410470950799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173492682363802940313967199 260239023545704410470950799)
  ·
    refine ⟨390358535318556615706426199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260239023545704410470950799 390358535318556615706426199)
    ·
      refine ⟨585537802977834923559639299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390358535318556615706426199 585537802977834923559639299)
      ·
        refine ⟨878306704466752385339458949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585537802977834923559639299 878306704466752385339458949)
        ·
          refine ⟨164682507087516072251148553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 878306704466752385339458949 164682507087516072251148553)
          ·
            refine ⟨123511880315637054188361415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164682507087516072251148553 123511880315637054188361415)
            ·
              refine ⟨185267820473455581282542123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123511880315637054188361415 185267820473455581282542123)
              ·
                refine ⟨277901730710183371923813185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185267820473455581282542123 277901730710183371923813185)
                ·
                  refine ⟨208426298032637528942859889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277901730710183371923813185 208426298032637528942859889)
                  ·
                    refine ⟨156319723524478146707144917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 208426298032637528942859889 156319723524478146707144917)
                    ·
                      refine ⟨3663743520104956563448709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156319723524478146707144917 3663743520104956563448709)
                      ·
                        rfl

theorem cell23_7135115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 7].length) (baseStart_7135115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135115 prefixEnd_7135115 := by exact prefixLift 7135115
  have htrace : WordTrace (prefixWord ++ tailWord_7135115) baseStart_7135115 baseEnd_7135115 := by
    simpa [prefixWord, tailWord_7135115, baseEnd_7135115] using wordTrace_append hprefix tailTrace_7135115
  have hstable : (prefixWord ++ tailWord_7135115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135115).length < 2 ^ (prefixWord ++ tailWord_7135115).sum := by decide
  have hdescent : baseEnd_7135115 < baseStart_7135115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135144 : List Nat := [2, 1, 6, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_7135144 : Nat := 118140960795 + 7135144 * 2 ^ 59
def prefixEnd_7135144 : Nat := 4983230072969 + 3 ^ 40 * 7135144 * 2
def baseEnd_7135144 : Nat := 3663758411043936949986077

theorem tailTrace_7135144 : CollatzResearch.WordTrace tailWord_7135144 prefixEnd_7135144 3663758411043936949986077 := by
  unfold tailWord_7135144
  simp only [CollatzResearch.WordTrace]
  refine ⟨130120040631299674211878243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173493387508399565615837657 130120040631299674211878243)
  ·
    refine ⟨195180060946949511317817365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130120040631299674211878243 195180060946949511317817365)
    ·
      refine ⟨9149065356888258343022689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 195180060946949511317817365 9149065356888258343022689)
      ·
        refine ⟨6861799017666193757267017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9149065356888258343022689 6861799017666193757267017)
        ·
          refine ⟨5146349263249645317950263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6861799017666193757267017 5146349263249645317950263)
          ·
            refine ⟨7719523894874467976925395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5146349263249645317950263 7719523894874467976925395)
            ·
              refine ⟨11579285842311701965388093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7719523894874467976925395 11579285842311701965388093)
              ·
                refine ⟨4342232190866888237020535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11579285842311701965388093 4342232190866888237020535)
                ·
                  refine ⟨6513348286300332355530803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4342232190866888237020535 6513348286300332355530803)
                  ·
                    refine ⟨9770022429450498533296205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6513348286300332355530803 9770022429450498533296205)
                    ·
                      refine ⟨3663758411043936949986077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9770022429450498533296205 3663758411043936949986077)
                      ·
                        rfl

theorem cell23_7135144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_7135144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135144 prefixEnd_7135144 := by exact prefixLift 7135144
  have htrace : WordTrace (prefixWord ++ tailWord_7135144) baseStart_7135144 baseEnd_7135144 := by
    simpa [prefixWord, tailWord_7135144, baseEnd_7135144] using wordTrace_append hprefix tailTrace_7135144
  have hstable : (prefixWord ++ tailWord_7135144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135144).length < 2 ^ (prefixWord ++ tailWord_7135144).sum := by decide
  have hdescent : baseEnd_7135144 < baseStart_7135144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135156 : List Nat := [2, 5, 2, 1, 2, 2, 9]
def baseStart_7135156 : Nat := 118140960795 + 7135156 * 2 ^ 59
def prefixEnd_7135156 : Nat := 4983230072969 + 3 ^ 40 * 7135156 * 2
def baseEnd_7135156 : Nat := 45231661392738159296741

theorem tailTrace_7135156 : CollatzResearch.WordTrace tailWord_7135156 prefixEnd_7135156 45231661392738159296741 := by
  unfold tailWord_7135156
  simp only [CollatzResearch.WordTrace]
  refine ⟨130120259469277937236596661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173493679292370582982128881 130120259469277937236596661)
  ·
    refine ⟨12198774325244806615930937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130120259469277937236596661 12198774325244806615930937)
    ·
      refine ⟨9149080743933604961948203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12198774325244806615930937 9149080743933604961948203)
      ·
        refine ⟨13723621115900407442922305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9149080743933604961948203 13723621115900407442922305)
        ·
          refine ⟨10292715836925305582191729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13723621115900407442922305 10292715836925305582191729)
          ·
            refine ⟨7719536877693979186643797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10292715836925305582191729 7719536877693979186643797)
            ·
              refine ⟨45231661392738159296741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7719536877693979186643797 45231661392738159296741)
              ·
                rfl

theorem cell23_7135156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 9].length) (baseStart_7135156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135156 prefixEnd_7135156 := by exact prefixLift 7135156
  have htrace : WordTrace (prefixWord ++ tailWord_7135156) baseStart_7135156 baseEnd_7135156 := by
    simpa [prefixWord, tailWord_7135156, baseEnd_7135156] using wordTrace_append hprefix tailTrace_7135156
  have hstable : (prefixWord ++ tailWord_7135156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135156).length < 2 ^ (prefixWord ++ tailWord_7135156).sum := by decide
  have hdescent : baseEnd_7135156 < baseStart_7135156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135159 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 5, 3, 2]
def baseStart_7135159 : Nat := 118140960795 + 7135159 * 2 ^ 59
def prefixEnd_7135159 : Nat := 4983230072969 + 3 ^ 40 * 7135159 * 2
def baseEnd_7135159 : Nat := 3663766113253754391298507

theorem tailTrace_7135159 : CollatzResearch.WordTrace tailWord_7135159 prefixEnd_7135159 3663766113253754391298507 := by
  unfold tailWord_7135159
  simp only [CollatzResearch.WordTrace]
  refine ⟨260240628357545005985552531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173493752238363337323701687 260240628357545005985552531)
  ·
    refine ⟨390360942536317508978328797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260240628357545005985552531 390360942536317508978328797)
    ·
      refine ⟨146385353451119065866873299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390360942536317508978328797 146385353451119065866873299)
      ·
        refine ⟨219578030176678598800309949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146385353451119065866873299 219578030176678598800309949)
        ·
          refine ⟨82341761316254474550116231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219578030176678598800309949 82341761316254474550116231)
          ·
            refine ⟨123512641974381711825174347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82341761316254474550116231 123512641974381711825174347)
            ·
              refine ⟨185268962961572567737761521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123512641974381711825174347 185268962961572567737761521)
              ·
                refine ⟨138951722221179425803321141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185268962961572567737761521 138951722221179425803321141)
                ·
                  refine ⟨13026723958235571169061357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138951722221179425803321141 13026723958235571169061357)
                  ·
                    refine ⟨4885021484338339188398009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13026723958235571169061357 4885021484338339188398009)
                    ·
                      refine ⟨3663766113253754391298507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4885021484338339188398009 3663766113253754391298507)
                      ·
                        rfl

theorem cell23_7135159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 3, 2].length) (baseStart_7135159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135159 prefixEnd_7135159 := by exact prefixLift 7135159
  have htrace : WordTrace (prefixWord ++ tailWord_7135159) baseStart_7135159 baseEnd_7135159 := by
    simpa [prefixWord, tailWord_7135159, baseEnd_7135159] using wordTrace_append hprefix tailTrace_7135159
  have hstable : (prefixWord ++ tailWord_7135159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135159).length < 2 ^ (prefixWord ++ tailWord_7135159).sum := by decide
  have hdescent : baseEnd_7135159 < baseStart_7135159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135166 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_7135166 : Nat := 118140960795 + 7135166 * 2 ^ 59
def prefixEnd_7135166 : Nat := 4983230072969 + 3 ^ 40 * 7135166 * 2
def baseEnd_7135166 : Nat := 3663769707618335863910975

theorem tailTrace_7135166 : CollatzResearch.WordTrace tailWord_7135166 prefixEnd_7135166 3663769707618335863910975 := by
  unfold tailWord_7135166
  simp only [CollatzResearch.WordTrace]
  refine ⟨32530110458564955772632169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173493922445679764120704901 32530110458564955772632169)
  ·
    refine ⟨24397582843923716829474127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32530110458564955772632169 24397582843923716829474127)
    ·
      refine ⟨36596374265885575244211191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24397582843923716829474127 36596374265885575244211191)
      ·
        refine ⟨54894561398828362866316787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36596374265885575244211191 54894561398828362866316787)
        ·
          refine ⟨82341842098242544299475181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54894561398828362866316787 82341842098242544299475181)
          ·
            refine ⟨30878190786840954112303193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82341842098242544299475181 30878190786840954112303193)
            ·
              refine ⟨23158643090130715584227395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30878190786840954112303193 23158643090130715584227395)
              ·
                refine ⟨34737964635196073376341093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23158643090130715584227395 34737964635196073376341093)
                ·
                  refine ⟨6513368369099263758063955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34737964635196073376341093 6513368369099263758063955)
                  ·
                    refine ⟨9770052553648895637095933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6513368369099263758063955 9770052553648895637095933)
                    ·
                      refine ⟨3663769707618335863910975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9770052553648895637095933 3663769707618335863910975)
                      ·
                        rfl

theorem cell23_7135166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_7135166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135166 prefixEnd_7135166 := by exact prefixLift 7135166
  have htrace : WordTrace (prefixWord ++ tailWord_7135166) baseStart_7135166 baseEnd_7135166 := by
    simpa [prefixWord, tailWord_7135166, baseEnd_7135166] using wordTrace_append hprefix tailTrace_7135166
  have hstable : (prefixWord ++ tailWord_7135166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135166).length < 2 ^ (prefixWord ++ tailWord_7135166).sum := by decide
  have hdescent : baseEnd_7135166 < baseStart_7135166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135182 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 1, 8]
def baseStart_7135182 : Nat := 118140960795 + 7135182 * 2 ^ 59
def prefixEnd_7135182 : Nat := 4983230072969 + 3 ^ 40 * 7135182 * 2
def baseEnd_7135182 : Nat := 1221259307769602600436967

theorem tailTrace_7135182 : CollatzResearch.WordTrace tailWord_7135182 prefixEnd_7135182 1221259307769602600436967 := by
  unfold tailWord_7135182
  simp only [CollatzResearch.WordTrace]
  refine ⟨32530183404557710114204975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173494311490974453942426533 32530183404557710114204975)
  ·
    refine ⟨48795275106836565171307463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32530183404557710114204975 48795275106836565171307463)
    ·
      refine ⟨73192912660254847756961195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48795275106836565171307463 73192912660254847756961195)
      ·
        refine ⟨109789368990382271635441793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73192912660254847756961195 109789368990382271635441793)
        ·
          refine ⟨82342026742786703726581345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109789368990382271635441793 82342026742786703726581345)
          ·
            refine ⟨61756520057090027794936009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82342026742786703726581345 61756520057090027794936009)
            ·
              refine ⟨46317390042817520846202007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61756520057090027794936009 46317390042817520846202007)
              ·
                refine ⟨69476085064226281269303011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46317390042817520846202007 69476085064226281269303011)
                ·
                  refine ⟨104214127596339421903954517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69476085064226281269303011 104214127596339421903954517)
                  ·
                    refine ⟨1221259307769602600436967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104214127596339421903954517 1221259307769602600436967)
                    ·
                      rfl

theorem cell23_7135182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_7135182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135182 prefixEnd_7135182 := by exact prefixLift 7135182
  have htrace : WordTrace (prefixWord ++ tailWord_7135182) baseStart_7135182 baseEnd_7135182 := by
    simpa [prefixWord, tailWord_7135182, baseEnd_7135182] using wordTrace_append hprefix tailTrace_7135182
  have hstable : (prefixWord ++ tailWord_7135182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135182).length < 2 ^ (prefixWord ++ tailWord_7135182).sum := by decide
  have hdescent : baseEnd_7135182 < baseStart_7135182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135192 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 4, 1, 5]
def baseStart_7135192 : Nat := 118140960795 + 7135192 * 2 ^ 59
def prefixEnd_7135192 : Nat := 4983230072969 + 3 ^ 40 * 7135192 * 2
def baseEnd_7135192 : Nat := 3663783058115352762185855

theorem tailTrace_7135192 : CollatzResearch.WordTrace tailWord_7135192 prefixEnd_7135192 3663783058115352762185855 := by
  unfold tailWord_7135192
  simp only [CollatzResearch.WordTrace]
  refine ⟨130120915983212726310751915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173494554644283635081002553 130120915983212726310751915)
  ·
    refine ⟨195181373974819089466127873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130120915983212726310751915 195181373974819089466127873)
    ·
      refine ⟨146386030481114317099595905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195181373974819089466127873 146386030481114317099595905)
      ·
        refine ⟨109789522860835737824696929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146386030481114317099595905 109789522860835737824696929)
        ·
          refine ⟨82342142145626803368522697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109789522860835737824696929 82342142145626803368522697)
          ·
            refine ⟨61756606609220102526392023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82342142145626803368522697 61756606609220102526392023)
            ·
              refine ⟨92634909913830153789588035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61756606609220102526392023 92634909913830153789588035)
              ·
                refine ⟨138952364870745230684382053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92634909913830153789588035 138952364870745230684382053)
                ·
                  refine ⟨26053568413264730753321635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138952364870745230684382053 26053568413264730753321635)
                  ·
                    refine ⟨39080352619897096129982453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26053568413264730753321635 39080352619897096129982453)
                    ·
                      refine ⟨3663783058115352762185855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39080352619897096129982453 3663783058115352762185855)
                      ·
                        rfl

theorem cell23_7135192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_7135192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135192 prefixEnd_7135192 := by exact prefixLift 7135192
  have htrace : WordTrace (prefixWord ++ tailWord_7135192) baseStart_7135192 baseEnd_7135192 := by
    simpa [prefixWord, tailWord_7135192, baseEnd_7135192] using wordTrace_append hprefix tailTrace_7135192
  have hstable : (prefixWord ++ tailWord_7135192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135192).length < 2 ^ (prefixWord ++ tailWord_7135192).sum := by decide
  have hdescent : baseEnd_7135192 < baseStart_7135192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135239 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 3]
def baseStart_7135239 : Nat := 118140960795 + 7135239 * 2 ^ 59
def prefixEnd_7135239 : Nat := 4983230072969 + 3 ^ 40 * 7135239 * 2
def baseEnd_7135239 : Nat := 3663807191706114078298139

theorem tailTrace_7135239 : CollatzResearch.WordTrace tailWord_7135239 prefixEnd_7135239 3663807191706114078298139 := by
  unfold tailWord_7135239
  simp only [CollatzResearch.WordTrace]
  refine ⟨260243546197255179648464771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173495697464836786432309847 260243546197255179648464771)
  ·
    refine ⟨390365319295882769472697157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260243546197255179648464771 390365319295882769472697157)
    ·
      refine ⟨73193497367978019276130717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 390365319295882769472697157 73193497367978019276130717)
      ·
        refine ⟨27447561512991757228549019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73193497367978019276130717 27447561512991757228549019)
        ·
          refine ⟨41171342269487635842823529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27447561512991757228549019 41171342269487635842823529)
          ·
            refine ⟨30878506702115726882117647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41171342269487635842823529 30878506702115726882117647)
            ·
              refine ⟨46317760053173590323176471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30878506702115726882117647 46317760053173590323176471)
              ·
                refine ⟨69476640079760385484764707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46317760053173590323176471 69476640079760385484764707)
                ·
                  refine ⟨104214960119640578227147061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69476640079760385484764707 104214960119640578227147061)
                  ·
                    refine ⟨9770152511216304208795037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104214960119640578227147061 9770152511216304208795037)
                    ·
                      refine ⟨3663807191706114078298139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9770152511216304208795037 3663807191706114078298139)
                      ·
                        rfl

theorem cell23_7135239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_7135239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135239 prefixEnd_7135239 := by exact prefixLift 7135239
  have htrace : WordTrace (prefixWord ++ tailWord_7135239) baseStart_7135239 baseEnd_7135239 := by
    simpa [prefixWord, tailWord_7135239, baseEnd_7135239] using wordTrace_append hprefix tailTrace_7135239
  have hstable : (prefixWord ++ tailWord_7135239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135239).length < 2 ^ (prefixWord ++ tailWord_7135239).sum := by decide
  have hdescent : baseEnd_7135239 < baseStart_7135239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135296 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 2, 4, 2]
def baseStart_7135296 : Nat := 118140960795 + 7135296 * 2 ^ 59
def prefixEnd_7135296 : Nat := 4983230072969 + 3 ^ 40 * 7135296 * 2
def baseEnd_7135296 : Nat := 3663836460103420355285377

theorem tailTrace_7135296 : CollatzResearch.WordTrace tailWord_7135296 prefixEnd_7135296 3663836460103420355285377 := by
  unfold tailWord_7135296
  simp only [CollatzResearch.WordTrace]
  refine ⟨130122812579024339191644871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173497083438699118922193161 130122812579024339191644871)
  ·
    refine ⟨195184218868536508787467307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130122812579024339191644871 195184218868536508787467307)
    ·
      refine ⟨292776328302804763181200961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195184218868536508787467307 292776328302804763181200961)
      ·
        refine ⟨219582246227103572385900721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292776328302804763181200961 219582246227103572385900721)
        ·
          refine ⟨164686684670327679289425541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219582246227103572385900721 164686684670327679289425541)
          ·
            refine ⟨30878753375686439866767289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164686684670327679289425541 30878753375686439866767289)
            ·
              refine ⟨23159065031764829900075467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30878753375686439866767289 23159065031764829900075467)
              ·
                refine ⟨34738597547647244850113201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23159065031764829900075467 34738597547647244850113201)
                ·
                  refine ⟨26053948160735433637584901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34738597547647244850113201 26053948160735433637584901)
                  ·
                    refine ⟨4885115280137893807047169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26053948160735433637584901 4885115280137893807047169)
                    ·
                      refine ⟨3663836460103420355285377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4885115280137893807047169 3663836460103420355285377)
                      ·
                        rfl

theorem cell23_7135296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 2, 4, 2].length) (baseStart_7135296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135296 prefixEnd_7135296 := by exact prefixLift 7135296
  have htrace : WordTrace (prefixWord ++ tailWord_7135296) baseStart_7135296 baseEnd_7135296 := by
    simpa [prefixWord, tailWord_7135296, baseEnd_7135296] using wordTrace_append hprefix tailTrace_7135296
  have hstable : (prefixWord ++ tailWord_7135296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135296).length < 2 ^ (prefixWord ++ tailWord_7135296).sum := by decide
  have hdescent : baseEnd_7135296 < baseStart_7135296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135299 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 3]
def baseStart_7135299 : Nat := 118140960795 + 7135299 * 2 ^ 59
def prefixEnd_7135299 : Nat := 4983230072969 + 3 ^ 40 * 7135299 * 2
def baseEnd_7135299 : Nat := 3663838000545383843547863

theorem tailTrace_7135299 : CollatzResearch.WordTrace tailWord_7135299 prefixEnd_7135299 3663838000545383843547863 := by
  unfold tailWord_7135299
  simp only [CollatzResearch.WordTrace]
  refine ⟨260245734577037809895648951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173497156384691873263765967 260245734577037809895648951)
  ·
    refine ⟨390368601865556714843473427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260245734577037809895648951 390368601865556714843473427)
    ·
      refine ⟨585552902798335072265210141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390368601865556714843473427 585552902798335072265210141)
      ·
        refine ⟨219582338549375652099453803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 585552902798335072265210141 219582338549375652099453803)
        ·
          refine ⟨329373507824063478149180705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219582338549375652099453803 329373507824063478149180705)
          ·
            refine ⟨247030130868047608611885529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329373507824063478149180705 247030130868047608611885529)
            ·
              refine ⟨185272598151035706458914147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247030130868047608611885529 185272598151035706458914147)
              ·
                refine ⟨277908897226553559688371221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185272598151035706458914147 277908897226553559688371221)
                ·
                  refine ⟨13026979557494698110392401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 277908897226553559688371221 13026979557494698110392401)
                  ·
                    refine ⟨9770234668121023582794301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13026979557494698110392401 9770234668121023582794301)
                    ·
                      refine ⟨3663838000545383843547863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9770234668121023582794301 3663838000545383843547863)
                      ·
                        rfl

theorem cell23_7135299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_7135299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135299 prefixEnd_7135299 := by exact prefixLift 7135299
  have htrace : WordTrace (prefixWord ++ tailWord_7135299) baseStart_7135299 baseEnd_7135299 := by
    simpa [prefixWord, tailWord_7135299, baseEnd_7135299] using wordTrace_append hprefix tailTrace_7135299
  have hstable : (prefixWord ++ tailWord_7135299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135299).length < 2 ^ (prefixWord ++ tailWord_7135299).sum := by decide
  have hdescent : baseEnd_7135299 < baseStart_7135299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135312 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 9]
def baseStart_7135312 : Nat := 118140960795 + 7135312 * 2 ^ 59
def prefixEnd_7135312 : Nat := 4983230072969 + 3 ^ 40 * 7135312 * 2
def baseEnd_7135312 : Nat := 3663844675793892292685303

theorem tailTrace_7135312 : CollatzResearch.WordTrace tailWord_7135312 prefixEnd_7135312 3663844675793892292685303 := by
  unfold tailWord_7135312
  simp only [CollatzResearch.WordTrace]
  refine ⟨130123104362995356557936095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173497472483993808743914793 130123104362995356557936095)
  ·
    refine ⟨195184656544493034836904143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130123104362995356557936095 195184656544493034836904143)
    ·
      refine ⟨292776984816739552255356215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195184656544493034836904143 292776984816739552255356215)
      ·
        refine ⟨439165477225109328383034323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292776984816739552255356215 439165477225109328383034323)
        ·
          refine ⟨658748215837663992574551485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439165477225109328383034323 658748215837663992574551485)
          ·
            refine ⟨247030580939123997215456807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 658748215837663992574551485 247030580939123997215456807)
            ·
              refine ⟨370545871408685995823185211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247030580939123997215456807 370545871408685995823185211)
              ·
                refine ⟨555818807113028993734777817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370545871408685995823185211 555818807113028993734777817)
                ·
                  refine ⟨416864105334771745301083363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555818807113028993734777817 416864105334771745301083363)
                  ·
                    refine ⟨625296158002157617951625045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 416864105334771745301083363 625296158002157617951625045)
                    ·
                      refine ⟨3663844675793892292685303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 625296158002157617951625045 3663844675793892292685303)
                      ·
                        rfl

theorem cell23_7135312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_7135312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135312 prefixEnd_7135312 := by exact prefixLift 7135312
  have htrace : WordTrace (prefixWord ++ tailWord_7135312) baseStart_7135312 baseEnd_7135312 := by
    simpa [prefixWord, tailWord_7135312, baseEnd_7135312] using wordTrace_append hprefix tailTrace_7135312
  have hstable : (prefixWord ++ tailWord_7135312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135312).length < 2 ^ (prefixWord ++ tailWord_7135312).sum := by decide
  have hdescent : baseEnd_7135312 < baseStart_7135312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135316 : List Nat := [2, 4, 1, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_7135316 : Nat := 118140960795 + 7135316 * 2 ^ 59
def prefixEnd_7135316 : Nat := 4983230072969 + 3 ^ 40 * 7135316 * 2
def baseEnd_7135316 : Nat := 3663846729716510277035285

theorem tailTrace_7135316 : CollatzResearch.WordTrace tailWord_7135316 prefixEnd_7135316 3663846729716510277035285 := by
  unfold tailWord_7135316
  simp only [CollatzResearch.WordTrace]
  refine ⟨130123177308988110899508901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173497569745317481199345201 130123177308988110899508901)
  ·
    refine ⟨24398095745435270793657919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130123177308988110899508901 24398095745435270793657919)
    ·
      refine ⟨36597143618152906190486879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24398095745435270793657919 36597143618152906190486879)
      ·
        refine ⟨54895715427229359285730319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36597143618152906190486879 54895715427229359285730319)
        ·
          refine ⟨82343573140844038928595479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54895715427229359285730319 82343573140844038928595479)
          ·
            refine ⟨123515359711266058392893219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82343573140844038928595479 123515359711266058392893219)
            ·
              refine ⟨185273039566899087589339829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123515359711266058392893219 185273039566899087589339829)
              ·
                refine ⟨17369347459396789461500609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185273039566899087589339829 17369347459396789461500609)
                ·
                  refine ⟨13027010594547592096125457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17369347459396789461500609 13027010594547592096125457)
                  ·
                    refine ⟨9770257945910694072094093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13027010594547592096125457 9770257945910694072094093)
                    ·
                      refine ⟨3663846729716510277035285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9770257945910694072094093 3663846729716510277035285)
                      ·
                        rfl

theorem cell23_7135316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_7135316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135316 prefixEnd_7135316 := by exact prefixLift 7135316
  have htrace : WordTrace (prefixWord ++ tailWord_7135316) baseStart_7135316 baseEnd_7135316 := by
    simpa [prefixWord, tailWord_7135316, baseEnd_7135316] using wordTrace_append hprefix tailTrace_7135316
  have hstable : (prefixWord ++ tailWord_7135316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135316).length < 2 ^ (prefixWord ++ tailWord_7135316).sum := by decide
  have hdescent : baseEnd_7135316 < baseStart_7135316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135340 : List Nat := [2, 2, 1, 1, 3, 4, 3, 2, 1, 4]
def baseStart_7135340 : Nat := 118140960795 + 7135340 * 2 ^ 59
def prefixEnd_7135340 : Nat := 4983230072969 + 3 ^ 40 * 7135340 * 2
def baseEnd_7135340 : Nat := 1221286351084072727711725

theorem tailTrace_7135340 : CollatzResearch.WordTrace tailWord_7135340 prefixEnd_7135340 1221286351084072727711725 := by
  unfold tailWord_7135340
  simp only [CollatzResearch.WordTrace]
  refine ⟨130123614984944636948945737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173498153313259515931927649 130123614984944636948945737)
  ·
    refine ⟨97592711238708477711709303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130123614984944636948945737 97592711238708477711709303)
    ·
      refine ⟨146389066858062716567563955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97592711238708477711709303 146389066858062716567563955)
      ·
        refine ⟨219583600287094074851345933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146389066858062716567563955 219583600287094074851345933)
        ·
          refine ⟨82343850107660278069254725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219583600287094074851345933 82343850107660278069254725)
          ·
            refine ⟨15439471895186302137985261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82343850107660278069254725 15439471895186302137985261)
            ·
              refine ⟨5789801960694863301744473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15439471895186302137985261 5789801960694863301744473)
              ·
                refine ⟨4342351470521147476308355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5789801960694863301744473 4342351470521147476308355)
                ·
                  refine ⟨6513527205781721214462533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4342351470521147476308355 6513527205781721214462533)
                  ·
                    refine ⟨1221286351084072727711725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6513527205781721214462533 1221286351084072727711725)
                    ·
                      rfl

theorem cell23_7135340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 1, 4].length) (baseStart_7135340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135340 prefixEnd_7135340 := by exact prefixLift 7135340
  have htrace : WordTrace (prefixWord ++ tailWord_7135340) baseStart_7135340 baseEnd_7135340 := by
    simpa [prefixWord, tailWord_7135340, baseEnd_7135340] using wordTrace_append hprefix tailTrace_7135340
  have hstable : (prefixWord ++ tailWord_7135340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135340).length < 2 ^ (prefixWord ++ tailWord_7135340).sum := by decide
  have hdescent : baseEnd_7135340 < baseStart_7135340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135353 : List Nat := [1, 2, 1, 3, 4, 3, 2, 1, 6]
def baseStart_7135353 : Nat := 118140960795 + 7135353 * 2 ^ 59
def prefixEnd_7135353 : Nat := 4983230072969 + 3 ^ 40 * 7135353 * 2
def baseEnd_7135353 : Nat := 407096192055636292474735

theorem tailTrace_7135353 : CollatzResearch.WordTrace tailWord_7135353 prefixEnd_7135353 407096192055636292474735 := by
  unfold tailWord_7135353
  simp only [CollatzResearch.WordTrace]
  refine ⟨260247704118842177118114713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173498469412561451412076475 260247704118842177118114713)
  ·
    refine ⟨195185778089131632838586035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260247704118842177118114713 195185778089131632838586035)
    ·
      refine ⟨292778667133697449257879053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195185778089131632838586035 292778667133697449257879053)
      ·
        refine ⟨109792000175136543471704645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292778667133697449257879053 109792000175136543471704645)
        ·
          refine ⟨20586000032838101900944621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109792000175136543471704645 20586000032838101900944621)
          ·
            refine ⟨7719750012314288212854233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20586000032838101900944621 7719750012314288212854233)
            ·
              refine ⟨5789812509235716159640675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7719750012314288212854233 5789812509235716159640675)
              ·
                refine ⟨8684718763853574239461013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5789812509235716159640675 8684718763853574239461013)
                ·
                  refine ⟨407096192055636292474735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8684718763853574239461013 407096192055636292474735)
                  ·
                    rfl

theorem cell23_7135353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 6].length) (baseStart_7135353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135353 prefixEnd_7135353 := by exact prefixLift 7135353
  have htrace : WordTrace (prefixWord ++ tailWord_7135353) baseStart_7135353 baseEnd_7135353 := by
    simpa [prefixWord, tailWord_7135353, baseEnd_7135353] using wordTrace_append hprefix tailTrace_7135353
  have hstable : (prefixWord ++ tailWord_7135353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135353).length < 2 ^ (prefixWord ++ tailWord_7135353).sum := by decide
  have hdescent : baseEnd_7135353 < baseStart_7135353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135416 : List Nat := [2, 1, 2, 1, 2, 1, 6, 1, 1, 2, 4]
def baseStart_7135416 : Nat := 118140960795 + 7135416 * 2 ^ 59
def prefixEnd_7135416 : Nat := 4983230072969 + 3 ^ 40 * 7135416 * 2
def baseEnd_7135416 : Nat := 3663898077781959885784825

theorem tailTrace_7135416 : CollatzResearch.WordTrace tailWord_7135416 prefixEnd_7135416 3663898077781959885784825 := by
  unfold tailWord_7135416
  simp only [CollatzResearch.WordTrace]
  refine ⟨130125000958806969438829051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173500001278409292585105401 130125000958806969438829051)
  ·
    refine ⟨195187501438210454158243577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130125000958806969438829051 195187501438210454158243577)
    ·
      refine ⟨146390626078657840618682683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195187501438210454158243577 146390626078657840618682683)
      ·
        refine ⟨219585939117986760928024025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146390626078657840618682683 219585939117986760928024025)
        ·
          refine ⟨164689454338490070696018019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219585939117986760928024025 164689454338490070696018019)
          ·
            refine ⟨247034181507735106044027029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164689454338490070696018019 247034181507735106044027029)
            ·
              refine ⟨11579727258175083095813767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 247034181507735106044027029 11579727258175083095813767)
              ·
                refine ⟨17369590887262624643720651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11579727258175083095813767 17369590887262624643720651)
                ·
                  refine ⟨26054386330893936965580977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17369590887262624643720651 26054386330893936965580977)
                  ·
                    refine ⟨19540789748170452724185733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26054386330893936965580977 19540789748170452724185733)
                    ·
                      refine ⟨3663898077781959885784825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19540789748170452724185733 3663898077781959885784825)
                      ·
                        rfl

theorem cell23_7135416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_7135416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135416 prefixEnd_7135416 := by exact prefixLift 7135416
  have htrace : WordTrace (prefixWord ++ tailWord_7135416) baseStart_7135416 baseEnd_7135416 := by
    simpa [prefixWord, tailWord_7135416, baseEnd_7135416] using wordTrace_append hprefix tailTrace_7135416
  have hstable : (prefixWord ++ tailWord_7135416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135416).length < 2 ^ (prefixWord ++ tailWord_7135416).sum := by decide
  have hdescent : baseEnd_7135416 < baseStart_7135416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135496 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_7135496 : Nat := 118140960795 + 7135496 * 2 ^ 59
def prefixEnd_7135496 : Nat := 4983230072969 + 3 ^ 40 * 7135496 * 2
def baseEnd_7135496 : Nat := 3663939156234319572784457

theorem tailTrace_7135496 : CollatzResearch.WordTrace tailWord_7135496 prefixEnd_7135496 3663939156234319572784457 := by
  unfold tailWord_7135496
  simp only [CollatzResearch.WordTrace]
  refine ⟨130126459878662056270285171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173501946504882741693713561 130126459878662056270285171)
  ·
    refine ⟨195189689817993084405427757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130126459878662056270285171 195189689817993084405427757)
    ·
      refine ⟨73196133681747406652035409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195189689817993084405427757 73196133681747406652035409)
      ·
        refine ⟨54897100261310554989026557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73196133681747406652035409 54897100261310554989026557)
        ·
          refine ⟨20586412597991458120884959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54897100261310554989026557 20586412597991458120884959)
          ·
            refine ⟨30879618896987187181327439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20586412597991458120884959 30879618896987187181327439)
            ·
              refine ⟨46319428345480780771991159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30879618896987187181327439 46319428345480780771991159)
              ·
                refine ⟨69479142518221171157986739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46319428345480780771991159 69479142518221171157986739)
                ·
                  refine ⟨104218713777331756736980109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69479142518221171157986739 104218713777331756736980109)
                  ·
                    refine ⟨39082017666499408776367541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104218713777331756736980109 39082017666499408776367541)
                    ·
                      refine ⟨3663939156234319572784457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39082017666499408776367541 3663939156234319572784457)
                      ·
                        rfl

theorem cell23_7135496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_7135496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135496 prefixEnd_7135496 := by exact prefixLift 7135496
  have htrace : WordTrace (prefixWord ++ tailWord_7135496) baseStart_7135496 baseEnd_7135496 := by
    simpa [prefixWord, tailWord_7135496, baseEnd_7135496] using wordTrace_append hprefix tailTrace_7135496
  have hstable : (prefixWord ++ tailWord_7135496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135496).length < 2 ^ (prefixWord ++ tailWord_7135496).sum := by decide
  have hdescent : baseEnd_7135496 < baseStart_7135496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135583 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 1, 6, 2]
def baseStart_7135583 : Nat := 118140960795 + 7135583 * 2 ^ 59
def prefixEnd_7135583 : Nat := 4983230072969 + 3 ^ 40 * 7135583 * 2
def baseEnd_7135583 : Nat := 3663983829051260732396557

theorem tailTrace_7135583 : CollatzResearch.WordTrace tailWord_7135583 prefixEnd_7135583 3663983829051260732396557 := by
  unfold tailWord_7135583
  simp only [CollatzResearch.WordTrace]
  refine ⟨260256092908008926398987403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173504061938672617599324935 260256092908008926398987403)
  ·
    refine ⟨390384139362013389598481105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260256092908008926398987403 390384139362013389598481105)
    ·
      refine ⟨292788104521510042198860829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390384139362013389598481105 292788104521510042198860829)
      ·
        refine ⟨109795539195566265824572811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292788104521510042198860829 109795539195566265824572811)
        ·
          refine ⟨164693308793349398736859217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109795539195566265824572811 164693308793349398736859217)
          ·
            refine ⟨123519981595012049052644413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164693308793349398736859217 123519981595012049052644413)
            ·
              refine ⟨46319993098129518394741655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123519981595012049052644413 46319993098129518394741655)
              ·
                refine ⟨69479989647194277592112483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46319993098129518394741655 69479989647194277592112483)
                ·
                  refine ⟨104219984470791416388168725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69479989647194277592112483 104219984470791416388168725)
                  ·
                    refine ⟨4885311772068347643195409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104219984470791416388168725 4885311772068347643195409)
                    ·
                      refine ⟨3663983829051260732396557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4885311772068347643195409 3663983829051260732396557)
                      ·
                        rfl

theorem cell23_7135583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_7135583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135583 prefixEnd_7135583 := by exact prefixLift 7135583
  have htrace : WordTrace (prefixWord ++ tailWord_7135583) baseStart_7135583 baseEnd_7135583 := by
    simpa [prefixWord, tailWord_7135583, baseEnd_7135583] using wordTrace_append hprefix tailTrace_7135583
  have hstable : (prefixWord ++ tailWord_7135583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135583).length < 2 ^ (prefixWord ++ tailWord_7135583).sum := by decide
  have hdescent : baseEnd_7135583 < baseStart_7135583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135593 : List Nat := [1, 2, 1, 1, 1, 3, 5, 2, 3, 4]
def baseStart_7135593 : Nat := 118140960795 + 7135593 * 2 ^ 59
def prefixEnd_7135593 : Nat := 4983230072969 + 3 ^ 40 * 7135593 * 2
def baseEnd_7135593 : Nat := 1221329654619268564423837

theorem tailTrace_7135593 : CollatzResearch.WordTrace tailWord_7135593 prefixEnd_7135593 1221329654619268564423837 := by
  unfold tailWord_7135593
  simp only [CollatzResearch.WordTrace]
  refine ⟨260256457637972698106851433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173504305091981798737900955 260256457637972698106851433)
  ·
    refine ⟨195192343228479523580138575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260256457637972698106851433 195192343228479523580138575)
    ·
      refine ⟨292788514842719285370207863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195192343228479523580138575 292788514842719285370207863)
      ·
        refine ⟨439182772264078928055311795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292788514842719285370207863 439182772264078928055311795)
        ·
          refine ⟨658774158396118392082967693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439182772264078928055311795 658774158396118392082967693)
          ·
            refine ⟨247040309398544397031112885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 658774158396118392082967693 247040309398544397031112885)
            ·
              refine ⟨23160029006113537221666833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 247040309398544397031112885 23160029006113537221666833)
              ·
                refine ⟨17370021754585152916250125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23160029006113537221666833 17370021754585152916250125)
                ·
                  refine ⟨6513758157969432343593797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17370021754585152916250125 6513758157969432343593797)
                  ·
                    refine ⟨1221329654619268564423837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6513758157969432343593797 1221329654619268564423837)
                    ·
                      rfl

theorem cell23_7135593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 4].length) (baseStart_7135593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135593 prefixEnd_7135593 := by exact prefixLift 7135593
  have htrace : WordTrace (prefixWord ++ tailWord_7135593) baseStart_7135593 baseEnd_7135593 := by
    simpa [prefixWord, tailWord_7135593, baseEnd_7135593] using wordTrace_append hprefix tailTrace_7135593
  have hstable : (prefixWord ++ tailWord_7135593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135593).length < 2 ^ (prefixWord ++ tailWord_7135593).sum := by decide
  have hdescent : baseEnd_7135593 < baseStart_7135593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135600 : List Nat := [2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 4]
def baseStart_7135600 : Nat := 118140960795 + 7135600 * 2 ^ 59
def prefixEnd_7135600 : Nat := 4983230072969 + 3 ^ 40 * 7135600 * 2
def baseEnd_7135600 : Nat := 3663992558222387165883979

theorem tailTrace_7135600 : CollatzResearch.WordTrace tailWord_7135600 prefixEnd_7135600 3663992558222387165883979 := by
  unfold tailWord_7135600
  simp only [CollatzResearch.WordTrace]
  refine ⟨130128356474473669151178127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173504475299298225534904169 130128356474473669151178127)
  ·
    refine ⟨195192534711710503726767191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130128356474473669151178127 195192534711710503726767191)
    ·
      refine ⟨292788802067565755590150787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195192534711710503726767191 292788802067565755590150787)
      ·
        refine ⟨439183203101348633385226181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292788802067565755590150787 439183203101348633385226181)
        ·
          refine ⟨82346850581502868759729909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 439183203101348633385226181 82346850581502868759729909)
          ·
            refine ⟨7720017242015893946224679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82346850581502868759729909 7720017242015893946224679)
            ·
              refine ⟨11580025863023840919337019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7720017242015893946224679 11580025863023840919337019)
              ·
                refine ⟨17370038794535761379005529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11580025863023840919337019 17370038794535761379005529)
                ·
                  refine ⟨13027529095901821034254147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17370038794535761379005529 13027529095901821034254147)
                  ·
                    refine ⟨19541293643852731551381221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13027529095901821034254147 19541293643852731551381221)
                    ·
                      refine ⟨3663992558222387165883979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19541293643852731551381221 3663992558222387165883979)
                      ·
                        rfl

theorem cell23_7135600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 4].length) (baseStart_7135600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135600 prefixEnd_7135600 := by exact prefixLift 7135600
  have htrace : WordTrace (prefixWord ++ tailWord_7135600) baseStart_7135600 baseEnd_7135600 := by
    simpa [prefixWord, tailWord_7135600, baseEnd_7135600] using wordTrace_append hprefix tailTrace_7135600
  have hstable : (prefixWord ++ tailWord_7135600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135600).length < 2 ^ (prefixWord ++ tailWord_7135600).sum := by decide
  have hdescent : baseEnd_7135600 < baseStart_7135600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135660 : List Nat := [2, 2, 1, 1, 1, 1, 3, 5, 2, 3, 2]
def baseStart_7135660 : Nat := 118140960795 + 7135660 * 2 ^ 59
def prefixEnd_7135660 : Nat := 4983230072969 + 3 ^ 40 * 7135660 * 2
def baseEnd_7135660 : Nat := 3664023367061656931133703

theorem tailTrace_7135660 : CollatzResearch.WordTrace tailWord_7135660 prefixEnd_7135660 3664023367061656931133703 := by
  unfold tailWord_7135660
  simp only [CollatzResearch.WordTrace]
  refine ⟨130129450664364984274770217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173505934219153312366360289 130129450664364984274770217)
  ·
    refine ⟨97597087998273738206077663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130129450664364984274770217 97597087998273738206077663)
    ·
      refine ⟨146395631997410607309116495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97597087998273738206077663 146395631997410607309116495)
      ·
        refine ⟨219593447996115910963674743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146395631997410607309116495 219593447996115910963674743)
        ·
          refine ⟨329390171994173866445512115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219593447996115910963674743 329390171994173866445512115)
          ·
            refine ⟨494085257991260799668268173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329390171994173866445512115 494085257991260799668268173)
            ·
              refine ⟨185281971746722799875600565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 494085257991260799668268173 185281971746722799875600565)
              ·
                refine ⟨17370184851255262488337553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185281971746722799875600565 17370184851255262488337553)
                ·
                  refine ⟨13027638638441446866253165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17370184851255262488337553 13027638638441446866253165)
                  ·
                    refine ⟨4885364489415542574844937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13027638638441446866253165 4885364489415542574844937)
                    ·
                      refine ⟨3664023367061656931133703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4885364489415542574844937 3664023367061656931133703)
                      ·
                        rfl

theorem cell23_7135660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 3, 2].length) (baseStart_7135660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135660 prefixEnd_7135660 := by exact prefixLift 7135660
  have htrace : WordTrace (prefixWord ++ tailWord_7135660) baseStart_7135660 baseEnd_7135660 := by
    simpa [prefixWord, tailWord_7135660, baseEnd_7135660] using wordTrace_append hprefix tailTrace_7135660
  have hstable : (prefixWord ++ tailWord_7135660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135660).length < 2 ^ (prefixWord ++ tailWord_7135660).sum := by decide
  have hdescent : baseEnd_7135660 < baseStart_7135660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135661 : List Nat := [1, 5, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_7135661 : Nat := 118140960795 + 7135661 * 2 ^ 59
def prefixEnd_7135661 : Nat := 4983230072969 + 3 ^ 40 * 7135661 * 2
def baseEnd_7135661 : Nat := 1221341293514103809073733

theorem tailTrace_7135661 : CollatzResearch.WordTrace tailWord_7135661 prefixEnd_7135661 1221341293514103809073733 := by
  unfold tailWord_7135661
  simp only [CollatzResearch.WordTrace]
  refine ⟨260258937801726345720326837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173505958534484230480217891 260258937801726345720326837)
  ·
    refine ⟨24399275418911844911280641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 260258937801726345720326837 24399275418911844911280641)
    ·
      refine ⟨18299456564183883683460481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24399275418911844911280641 18299456564183883683460481)
      ·
        refine ⟨13724592423137912762595361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18299456564183883683460481 13724592423137912762595361)
        ·
          refine ⟨10293444317353434571946521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13724592423137912762595361 10293444317353434571946521)
          ·
            refine ⟨7720083238015075928959891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10293444317353434571946521 7720083238015075928959891)
            ·
              refine ⟨11580124857022613893439837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7720083238015075928959891 11580124857022613893439837)
              ·
                refine ⟨4342546821383480210039939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11580124857022613893439837 4342546821383480210039939)
                ·
                  refine ⟨6513820232075220315059909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4342546821383480210039939 6513820232075220315059909)
                  ·
                    refine ⟨1221341293514103809073733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6513820232075220315059909 1221341293514103809073733)
                    ·
                      rfl

theorem cell23_7135661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_7135661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135661 prefixEnd_7135661 := by exact prefixLift 7135661
  have htrace : WordTrace (prefixWord ++ tailWord_7135661) baseStart_7135661 baseEnd_7135661 := by
    simpa [prefixWord, tailWord_7135661, baseEnd_7135661] using wordTrace_append hprefix tailTrace_7135661
  have hstable : (prefixWord ++ tailWord_7135661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135661).length < 2 ^ (prefixWord ++ tailWord_7135661).sum := by decide
  have hdescent : baseEnd_7135661 < baseStart_7135661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135677 : List Nat := [1, 4, 1, 2, 2, 3, 1, 2, 2, 3, 2]
def baseStart_7135677 : Nat := 118140960795 + 7135677 * 2 ^ 59
def prefixEnd_7135677 : Nat := 4983230072969 + 3 ^ 40 * 7135677 * 2
def baseEnd_7135677 : Nat := 3664032096232783364621125

theorem tailTrace_7135677 : CollatzResearch.WordTrace tailWord_7135677 prefixEnd_7135677 3664032096232783364621125 := by
  unfold tailWord_7135677
  simp only [CollatzResearch.WordTrace]
  refine ⟨260259521369668380452909285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173506347579778920301939523 260259521369668380452909285)
  ·
    refine ⟨48798660256812821334920491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260259521369668380452909285 48798660256812821334920491)
    ·
      refine ⟨73197990385219232002380737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48798660256812821334920491 73197990385219232002380737)
      ·
        refine ⟨54898492788914424001785553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73197990385219232002380737 54898492788914424001785553)
        ·
          refine ⟨41173869591685818001339165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54898492788914424001785553 41173869591685818001339165)
          ·
            refine ⟨15440201096882181750502187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41173869591685818001339165 15440201096882181750502187)
            ·
              refine ⟨23160301645323272625753281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15440201096882181750502187 23160301645323272625753281)
              ·
                refine ⟨17370226233992454469314961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23160301645323272625753281 17370226233992454469314961)
                ·
                  refine ⟨13027669675494340851986221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17370226233992454469314961 13027669675494340851986221)
                  ·
                    refine ⟨4885376128310377819494833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13027669675494340851986221 4885376128310377819494833)
                    ·
                      refine ⟨3664032096232783364621125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4885376128310377819494833 3664032096232783364621125)
                      ·
                        rfl

theorem cell23_7135677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_7135677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135677 prefixEnd_7135677 := by exact prefixLift 7135677
  have htrace : WordTrace (prefixWord ++ tailWord_7135677) baseStart_7135677 baseEnd_7135677 := by
    simpa [prefixWord, tailWord_7135677, baseEnd_7135677] using wordTrace_append hprefix tailTrace_7135677
  have hstable : (prefixWord ++ tailWord_7135677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135677).length < 2 ^ (prefixWord ++ tailWord_7135677).sum := by decide
  have hdescent : baseEnd_7135677 < baseStart_7135677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135720 : List Nat := [2, 1, 4, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_7135720 : Nat := 118140960795 + 7135720 * 2 ^ 59
def prefixEnd_7135720 : Nat := 4983230072969 + 3 ^ 40 * 7135720 * 2
def baseEnd_7135720 : Nat := 3664054175900926696383427

theorem tailTrace_7135720 : CollatzResearch.WordTrace tailWord_7135720 prefixEnd_7135720 3664054175900926696383427 := by
  unfold tailWord_7135720
  simp only [CollatzResearch.WordTrace]
  refine ⟨130130544854256299398362307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173507393139008399197816409 130130544854256299398362307)
  ·
    refine ⟨195195817281384449097543461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130130544854256299398362307 195195817281384449097543461)
    ·
      refine ⟨36599215740259584205789399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195195817281384449097543461 36599215740259584205789399)
      ·
        refine ⟨54898823610389376308684099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36599215740259584205789399 54898823610389376308684099)
        ·
          refine ⟨82348235415584064463026149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54898823610389376308684099 82348235415584064463026149)
          ·
            refine ⟨15440294140422012086817403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82348235415584064463026149 15440294140422012086817403)
            ·
              refine ⟨23160441210633018130226105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15440294140422012086817403 23160441210633018130226105)
              ·
                refine ⟨17370330907974763597669579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23160441210633018130226105 17370330907974763597669579)
                ·
                  refine ⟨26055496361962145396504369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17370330907974763597669579 26055496361962145396504369)
                  ·
                    refine ⟨19541622271471609047378277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26055496361962145396504369 19541622271471609047378277)
                    ·
                      refine ⟨3664054175900926696383427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19541622271471609047378277 3664054175900926696383427)
                      ·
                        rfl

theorem cell23_7135720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_7135720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135720 prefixEnd_7135720 := by exact prefixLift 7135720
  have htrace : WordTrace (prefixWord ++ tailWord_7135720) baseStart_7135720 baseEnd_7135720 := by
    simpa [prefixWord, tailWord_7135720, baseEnd_7135720] using wordTrace_append hprefix tailTrace_7135720
  have hstable : (prefixWord ++ tailWord_7135720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135720).length < 2 ^ (prefixWord ++ tailWord_7135720).sum := by decide
  have hdescent : baseEnd_7135720 < baseStart_7135720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135724 : List Nat := [2, 2, 1, 1, 2, 1, 4, 5, 1, 2, 2]
def baseStart_7135724 : Nat := 118140960795 + 7135724 * 2 ^ 59
def prefixEnd_7135724 : Nat := 4983230072969 + 3 ^ 40 * 7135724 * 2
def baseEnd_7135724 : Nat := 3664056229823544680733409

theorem tailTrace_7135724 : CollatzResearch.WordTrace tailWord_7135724 prefixEnd_7135724 3664056229823544680733409 := by
  unfold tailWord_7135724
  simp only [CollatzResearch.WordTrace]
  refine ⟨130130617800249053739935113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173507490400332071653246817 130130617800249053739935113)
  ·
    refine ⟨97597963350186790304951335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130130617800249053739935113 97597963350186790304951335)
    ·
      refine ⟨146396945025280185457427003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97597963350186790304951335 146396945025280185457427003)
      ·
        refine ⟨219595417537920278186140505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146396945025280185457427003 219595417537920278186140505)
        ·
          refine ⟨164696563153440208639605379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219595417537920278186140505 164696563153440208639605379)
          ·
            refine ⟨247044844730160312959408069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164696563153440208639605379 247044844730160312959408069)
            ·
              refine ⟨46320908386905058679889013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247044844730160312959408069 46320908386905058679889013)
              ·
                refine ⟨4342585161272349251239595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46320908386905058679889013 4342585161272349251239595)
                ·
                  refine ⟨6513877741908523876859393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4342585161272349251239595 6513877741908523876859393)
                  ·
                    refine ⟨4885408306431392907644545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6513877741908523876859393 4885408306431392907644545)
                    ·
                      refine ⟨3664056229823544680733409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4885408306431392907644545 3664056229823544680733409)
                      ·
                        rfl

theorem cell23_7135724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 1, 2, 2].length) (baseStart_7135724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135724 prefixEnd_7135724 := by exact prefixLift 7135724
  have htrace : WordTrace (prefixWord ++ tailWord_7135724) baseStart_7135724 baseEnd_7135724 := by
    simpa [prefixWord, tailWord_7135724, baseEnd_7135724] using wordTrace_append hprefix tailTrace_7135724
  have hstable : (prefixWord ++ tailWord_7135724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135724).length < 2 ^ (prefixWord ++ tailWord_7135724).sum := by decide
  have hdescent : baseEnd_7135724 < baseStart_7135724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135730 : List Nat := [3, 2, 1, 4, 3, 10]
def baseStart_7135730 : Nat := 118140960795 + 7135730 * 2 ^ 59
def prefixEnd_7135730 : Nat := 4983230072969 + 3 ^ 40 * 7135730 * 2
def baseEnd_7135730 : Nat := 15078433377397002704767

theorem tailTrace_7135730 : CollatzResearch.WordTrace tailWord_7135730 prefixEnd_7135730 15078433377397002704767 := by
  unfold tailWord_7135730
  simp only [CollatzResearch.WordTrace]
  refine ⟨65065363609619092626147161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173507636292317580336392429 65065363609619092626147161)
  ·
    refine ⟨48799022707214319469610371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65065363609619092626147161 48799022707214319469610371)
    ·
      refine ⟨73198534060821479204415557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48799022707214319469610371 73198534060821479204415557)
      ·
        refine ⟨13724725136404027350827917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73198534060821479204415557 13724725136404027350827917)
        ·
          refine ⟨5146771926151510256560469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13724725136404027350827917 5146771926151510256560469)
          ·
            refine ⟨15078433377397002704767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5146771926151510256560469 15078433377397002704767)
            ·
              rfl

theorem cell23_7135730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 10].length) (baseStart_7135730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135730 prefixEnd_7135730 := by exact prefixLift 7135730
  have htrace : WordTrace (prefixWord ++ tailWord_7135730) baseStart_7135730 baseEnd_7135730 := by
    simpa [prefixWord, tailWord_7135730, baseEnd_7135730] using wordTrace_append hprefix tailTrace_7135730
  have hstable : (prefixWord ++ tailWord_7135730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135730).length < 2 ^ (prefixWord ++ tailWord_7135730).sum := by decide
  have hdescent : baseEnd_7135730 < baseStart_7135730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135763 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 4]
def baseStart_7135763 : Nat := 118140960795 + 7135763 * 2 ^ 59
def prefixEnd_7135763 : Nat := 4983230072969 + 3 ^ 40 * 7135763 * 2
def baseEnd_7135763 : Nat := 3664076255569070028145729

theorem tailTrace_7135763 : CollatzResearch.WordTrace tailWord_7135763 prefixEnd_7135763 3664076255569070028145729 := by
  unfold tailWord_7135763
  simp only [CollatzResearch.WordTrace]
  refine ⟨260262658047356817140539943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173508438698237878093693295 260262658047356817140539943)
  ·
    refine ⟨390393987071035225710809915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260262658047356817140539943 390393987071035225710809915)
    ·
      refine ⟨585590980606552838566214873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390393987071035225710809915 585590980606552838566214873)
      ·
        refine ⟨439193235454914628924661155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585590980606552838566214873 439193235454914628924661155)
        ·
          refine ⟨658789853182371943386991733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439193235454914628924661155 658789853182371943386991733)
          ·
            refine ⟨61761548735847369692530475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 658789853182371943386991733 61761548735847369692530475)
            ·
              refine ⟨92642323103771054538795713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61761548735847369692530475 92642323103771054538795713)
              ·
                refine ⟨69481742327828290904096785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92642323103771054538795713 69481742327828290904096785)
                ·
                  refine ⟨52111306745871218178072589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69481742327828290904096785 52111306745871218178072589)
                  ·
                    refine ⟨19541740029701706816777221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52111306745871218178072589 19541740029701706816777221)
                    ·
                      refine ⟨3664076255569070028145729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19541740029701706816777221 3664076255569070028145729)
                      ·
                        rfl

theorem cell23_7135763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_7135763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135763 prefixEnd_7135763 := by exact prefixLift 7135763
  have htrace : WordTrace (prefixWord ++ tailWord_7135763) baseStart_7135763 baseEnd_7135763 := by
    simpa [prefixWord, tailWord_7135763, baseEnd_7135763] using wordTrace_append hprefix tailTrace_7135763
  have hstable : (prefixWord ++ tailWord_7135763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135763).length < 2 ^ (prefixWord ++ tailWord_7135763).sum := by decide
  have hdescent : baseEnd_7135763 < baseStart_7135763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135920 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 3]
def baseStart_7135920 : Nat := 118140960795 + 7135920 * 2 ^ 59
def prefixEnd_7135920 : Nat := 4983230072969 + 3 ^ 40 * 7135920 * 2
def baseEnd_7135920 : Nat := 3664156872031825913882507

theorem tailTrace_7135920 : CollatzResearch.WordTrace tailWord_7135920 prefixEnd_7135920 3664156872031825913882507 := by
  unfold tailWord_7135920
  simp only [CollatzResearch.WordTrace]
  refine ⟨130134192153894016477002607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173512256205192021969336809 130134192153894016477002607)
  ·
    refine ⟨195201288230841024715503911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130134192153894016477002607 195201288230841024715503911)
    ·
      refine ⟨292801932346261537073255867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195201288230841024715503911 292801932346261537073255867)
      ·
        refine ⟨439202898519392305609883801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292801932346261537073255867 439202898519392305609883801)
        ·
          refine ⟨329402173889544229207412851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439202898519392305609883801 329402173889544229207412851)
          ·
            refine ⟨494103260834316343811119277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329402173889544229207412851 494103260834316343811119277)
            ·
              refine ⟨185288722812868628929169729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 494103260834316343811119277 185288722812868628929169729)
              ·
                refine ⟨138966542109651471696877297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185288722812868628929169729 138966542109651471696877297)
                ·
                  refine ⟨104224906582238603772657973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138966542109651471696877297 104224906582238603772657973)
                  ·
                    refine ⟨9771084992084869103686685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104224906582238603772657973 9771084992084869103686685)
                    ·
                      refine ⟨3664156872031825913882507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9771084992084869103686685 3664156872031825913882507)
                      ·
                        rfl

theorem cell23_7135920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 3].length) (baseStart_7135920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135920 prefixEnd_7135920 := by exact prefixLift 7135920
  have htrace : WordTrace (prefixWord ++ tailWord_7135920) baseStart_7135920 baseEnd_7135920 := by
    simpa [prefixWord, tailWord_7135920, baseEnd_7135920] using wordTrace_append hprefix tailTrace_7135920
  have hstable : (prefixWord ++ tailWord_7135920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135920).length < 2 ^ (prefixWord ++ tailWord_7135920).sum := by decide
  have hdescent : baseEnd_7135920 < baseStart_7135920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135921 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 2, 4, 2]
def baseStart_7135921 : Nat := 118140960795 + 7135921 * 2 ^ 59
def prefixEnd_7135921 : Nat := 4983230072969 + 3 ^ 40 * 7135921 * 2
def baseEnd_7135921 : Nat := 3664157385512480409970003

theorem tailTrace_7135921 : CollatzResearch.WordTrace tailWord_7135921 prefixEnd_7135921 3664157385512480409970003 := by
  unfold tailWord_7135921
  simp only [CollatzResearch.WordTrace]
  refine ⟨260268420780784410124791617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173512280520522940083194411 260268420780784410124791617)
  ·
    refine ⟨195201315585588307593593713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260268420780784410124791617 195201315585588307593593713)
    ·
      refine ⟨146400986689191230695195285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195201315585588307593593713 146400986689191230695195285)
      ·
        refine ⟨6862546251055838938837279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146400986689191230695195285 6862546251055838938837279)
        ·
          refine ⟨10293819376583758408255919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6862546251055838938837279 10293819376583758408255919)
          ·
            refine ⟨15440729064875637612383879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10293819376583758408255919 15440729064875637612383879)
            ·
              refine ⟨23161093597313456418575819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15440729064875637612383879 23161093597313456418575819)
              ·
                refine ⟨34741640395970184627863729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23161093597313456418575819 34741640395970184627863729)
                ·
                  refine ⟨26056230296977638470897797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34741640395970184627863729 26056230296977638470897797)
                  ·
                    refine ⟨4885543180683307213293337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26056230296977638470897797 4885543180683307213293337)
                    ·
                      refine ⟨3664157385512480409970003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4885543180683307213293337 3664157385512480409970003)
                      ·
                        rfl

theorem cell23_7135921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_7135921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135921 prefixEnd_7135921 := by exact prefixLift 7135921
  have htrace : WordTrace (prefixWord ++ tailWord_7135921) baseStart_7135921 baseEnd_7135921 := by
    simpa [prefixWord, tailWord_7135921, baseEnd_7135921] using wordTrace_append hprefix tailTrace_7135921
  have hstable : (prefixWord ++ tailWord_7135921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135921).length < 2 ^ (prefixWord ++ tailWord_7135921).sum := by decide
  have hdescent : baseEnd_7135921 < baseStart_7135921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7135971 : List Nat := [1, 1, 1, 7, 1, 2, 2, 1, 3, 1, 3]
def baseStart_7135971 : Nat := 118140960795 + 7135971 * 2 ^ 59
def prefixEnd_7135971 : Nat := 4983230072969 + 3 ^ 40 * 7135971 * 2
def baseEnd_7135971 : Nat := 3664183059545205214344773

theorem tailTrace_7135971 : CollatzResearch.WordTrace tailWord_7135971 prefixEnd_7135971 3664183059545205214344773 := by
  unfold tailWord_7135971
  simp only [CollatzResearch.WordTrace]
  refine ⟨260270244430603268664111767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173513496287068845776074511 260270244430603268664111767)
  ·
    refine ⟨390405366645904902996167651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260270244430603268664111767 390405366645904902996167651)
    ·
      refine ⟨585608049968857354494251477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390405366645904902996167651 585608049968857354494251477)
      ·
        refine ⟨13725188671145094245959019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 585608049968857354494251477 13725188671145094245959019)
        ·
          refine ⟨20587783006717641368938529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13725188671145094245959019 20587783006717641368938529)
          ·
            refine ⟨15440837255038231026703897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20587783006717641368938529 15440837255038231026703897)
            ·
              refine ⟨11580627941278673270027923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15440837255038231026703897 11580627941278673270027923)
              ·
                refine ⟨17370941911918009905041885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11580627941278673270027923 17370941911918009905041885)
                ·
                  refine ⟨6514103216969253714390707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17370941911918009905041885 6514103216969253714390707)
                  ·
                    refine ⟨9771154825453880571586061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6514103216969253714390707 9771154825453880571586061)
                    ·
                      refine ⟨3664183059545205214344773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9771154825453880571586061 3664183059545205214344773)
                      ·
                        rfl

theorem cell23_7135971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_7135971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7135971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7135971 prefixEnd_7135971 := by exact prefixLift 7135971
  have htrace : WordTrace (prefixWord ++ tailWord_7135971) baseStart_7135971 baseEnd_7135971 := by
    simpa [prefixWord, tailWord_7135971, baseEnd_7135971] using wordTrace_append hprefix tailTrace_7135971
  have hstable : (prefixWord ++ tailWord_7135971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7135971).length < 2 ^ (prefixWord ++ tailWord_7135971).sum := by decide
  have hdescent : baseEnd_7135971 < baseStart_7135971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7135971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136028 : List Nat := [2, 2, 3, 1, 1, 5, 1, 1, 3, 2, 2]
def baseStart_7136028 : Nat := 118140960795 + 7136028 * 2 ^ 59
def prefixEnd_7136028 : Nat := 4983230072969 + 3 ^ 40 * 7136028 * 2
def baseEnd_7136028 : Nat := 3664212327942511491332011

theorem tailTrace_7136028 : CollatzResearch.WordTrace tailWord_7136028 prefixEnd_7136028 3664212327942511491332011 := by
  unfold tailWord_7136028
  simp only [CollatzResearch.WordTrace]
  refine ⟨130136161695698383699468369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173514882260931178265957825 130136161695698383699468369)
  ·
    refine ⟨97602121271773787774601277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130136161695698383699468369 97602121271773787774601277)
    ·
      refine ⟨36600795476915170415475479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97602121271773787774601277 36600795476915170415475479)
      ·
        refine ⟨54901193215372755623213219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36600795476915170415475479 54901193215372755623213219)
        ·
          refine ⟨82351789823059133434819829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54901193215372755623213219 82351789823059133434819829)
          ·
            refine ⟨7720480295911793759514359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82351789823059133434819829 7720480295911793759514359)
            ·
              refine ⟨11580720443867690639271539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7720480295911793759514359 11580720443867690639271539)
              ·
                refine ⟨17371080665801535958907309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11580720443867690639271539 17371080665801535958907309)
                ·
                  refine ⟨6514155249675575984590241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17371080665801535958907309 6514155249675575984590241)
                  ·
                    refine ⟨4885616437256681988442681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6514155249675575984590241 4885616437256681988442681)
                    ·
                      refine ⟨3664212327942511491332011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4885616437256681988442681 3664212327942511491332011)
                      ·
                        rfl

theorem cell23_7136028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_7136028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136028 prefixEnd_7136028 := by exact prefixLift 7136028
  have htrace : WordTrace (prefixWord ++ tailWord_7136028) baseStart_7136028 baseEnd_7136028 := by
    simpa [prefixWord, tailWord_7136028, baseEnd_7136028] using wordTrace_append hprefix tailTrace_7136028
  have hstable : (prefixWord ++ tailWord_7136028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136028).length < 2 ^ (prefixWord ++ tailWord_7136028).sum := by decide
  have hdescent : baseEnd_7136028 < baseStart_7136028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136045 : List Nat := [1, 5, 3, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_7136045 : Nat := 118140960795 + 7136045 * 2 ^ 59
def prefixEnd_7136045 : Nat := 4983230072969 + 3 ^ 40 * 7136045 * 2
def baseEnd_7136045 : Nat := 3664221057113637924819433

theorem tailTrace_7136045 : CollatzResearch.WordTrace tailWord_7136045 prefixEnd_7136045 3664221057113637924819433 := by
  unfold tailWord_7136045
  simp only [CollatzResearch.WordTrace]
  refine ⟨260272943432335179302305589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173515295621556786201537059 260272943432335179302305589)
  ·
    refine ⟨24400588446781423059591149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 260272943432335179302305589 24400588446781423059591149)
    ·
      refine ⟨9150220667543033647346681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24400588446781423059591149 9150220667543033647346681)
      ·
        refine ⟨6862665500657275235510011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9150220667543033647346681 6862665500657275235510011)
        ·
          refine ⟨10293998250985912853265017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6862665500657275235510011 10293998250985912853265017)
          ·
            refine ⟨7720498688239434639948763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10293998250985912853265017 7720498688239434639948763)
            ·
              refine ⟨11580748032359151959923145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7720498688239434639948763 11580748032359151959923145)
              ·
                refine ⟨8685561024269363969942359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11580748032359151959923145 8685561024269363969942359)
                ·
                  refine ⟨13028341536404045954913539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8685561024269363969942359 13028341536404045954913539)
                  ·
                    refine ⟨19542512304606068932370309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13028341536404045954913539 19542512304606068932370309)
                    ·
                      refine ⟨3664221057113637924819433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19542512304606068932370309 3664221057113637924819433)
                      ·
                        rfl

theorem cell23_7136045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_7136045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136045 prefixEnd_7136045 := by exact prefixLift 7136045
  have htrace : WordTrace (prefixWord ++ tailWord_7136045) baseStart_7136045 baseEnd_7136045 := by
    simpa [prefixWord, tailWord_7136045, baseEnd_7136045] using wordTrace_append hprefix tailTrace_7136045
  have hstable : (prefixWord ++ tailWord_7136045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136045).length < 2 ^ (prefixWord ++ tailWord_7136045).sum := by decide
  have hdescent : baseEnd_7136045 < baseStart_7136045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136061 : List Nat := [1, 4, 1, 4, 2, 1, 1, 2, 1, 3, 3]
def baseStart_7136061 : Nat := 118140960795 + 7136061 * 2 ^ 59
def prefixEnd_7136061 : Nat := 4983230072969 + 3 ^ 40 * 7136061 * 2
def baseEnd_7136061 : Nat := 3664229272804109862219359

theorem tailTrace_7136061 : CollatzResearch.WordTrace tailWord_7136061 prefixEnd_7136061 3664229272804109862219359 := by
  unfold tailWord_7136061
  simp only [CollatzResearch.WordTrace]
  refine ⟨260273527000277214034888037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173515684666851476023258691 260273527000277214034888037)
  ·
    refine ⟨48801286312551977631541507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260273527000277214034888037 48801286312551977631541507)
    ·
      refine ⟨73201929468827966447312261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48801286312551977631541507 73201929468827966447312261)
      ·
        refine ⟨13725361775405243708871049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73201929468827966447312261 13725361775405243708871049)
        ·
          refine ⟨10294021331553932781653287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13725361775405243708871049 10294021331553932781653287)
          ·
            refine ⟨15441031997330899172479931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10294021331553932781653287 15441031997330899172479931)
            ·
              refine ⟨23161547995996348758719897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15441031997330899172479931 23161547995996348758719897)
              ·
                refine ⟨17371160996997261569039923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23161547995996348758719897 17371160996997261569039923)
                ·
                  refine ⟨26056741495495892353559885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17371160996997261569039923 26056741495495892353559885)
                  ·
                    refine ⟨9771278060810959632584957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26056741495495892353559885 9771278060810959632584957)
                    ·
                      refine ⟨3664229272804109862219359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9771278060810959632584957 3664229272804109862219359)
                      ·
                        rfl

theorem cell23_7136061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_7136061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136061 prefixEnd_7136061 := by exact prefixLift 7136061
  have htrace : WordTrace (prefixWord ++ tailWord_7136061) baseStart_7136061 baseEnd_7136061 := by
    simpa [prefixWord, tailWord_7136061, baseEnd_7136061] using wordTrace_append hprefix tailTrace_7136061
  have hstable : (prefixWord ++ tailWord_7136061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136061).length < 2 ^ (prefixWord ++ tailWord_7136061).sum := by decide
  have hdescent : baseEnd_7136061 < baseStart_7136061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136065 : List Nat := [1, 2, 5, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_7136065 : Nat := 118140960795 + 7136065 * 2 ^ 59
def prefixEnd_7136065 : Nat := 4983230072969 + 3 ^ 40 * 7136065 * 2
def baseEnd_7136065 : Nat := 3664231326726727846569341

theorem tailTrace_7136065 : CollatzResearch.WordTrace tailWord_7136065 prefixEnd_7136065 3664231326726727846569341 := by
  unfold tailWord_7136065
  simp only [CollatzResearch.WordTrace]
  refine ⟨260273672892262722718033649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173515781928175148478689099 260273672892262722718033649)
  ·
    refine ⟨195205254669197042038525237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260273672892262722718033649 195205254669197042038525237)
    ·
      refine ⟨18300492625237222691111741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195205254669197042038525237 18300492625237222691111741)
      ·
        refine ⟨6862684734463958509166903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18300492625237222691111741 6862684734463958509166903)
        ·
          refine ⟨10294027101695937763750355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6862684734463958509166903 10294027101695937763750355)
          ·
            refine ⟨15441040652543906645625533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10294027101695937763750355 15441040652543906645625533)
            ·
              refine ⟨5790390244703964992109575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15441040652543906645625533 5790390244703964992109575)
              ·
                refine ⟨8685585367055947488164363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5790390244703964992109575 8685585367055947488164363)
                ·
                  refine ⟨13028378050583921232246545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8685585367055947488164363 13028378050583921232246545)
                  ·
                    refine ⟨9771283537937940924184909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13028378050583921232246545 9771283537937940924184909)
                    ·
                      refine ⟨3664231326726727846569341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9771283537937940924184909 3664231326726727846569341)
                      ·
                        rfl

theorem cell23_7136065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_7136065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136065 prefixEnd_7136065 := by exact prefixLift 7136065
  have htrace : WordTrace (prefixWord ++ tailWord_7136065) baseStart_7136065 baseEnd_7136065 := by
    simpa [prefixWord, tailWord_7136065, baseEnd_7136065] using wordTrace_append hprefix tailTrace_7136065
  have hstable : (prefixWord ++ tailWord_7136065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136065).length < 2 ^ (prefixWord ++ tailWord_7136065).sum := by decide
  have hdescent : baseEnd_7136065 < baseStart_7136065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136118 : List Nat := [5, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2]
def baseStart_7136118 : Nat := 118140960795 + 7136118 * 2 ^ 59
def prefixEnd_7136118 : Nat := 4983230072969 + 3 ^ 40 * 7136118 * 2
def baseEnd_7136118 : Nat := 3664258541201416139206597

theorem tailTrace_7136118 : CollatzResearch.WordTrace tailWord_7136118 prefixEnd_7136118 3664258541201416139206597 := by
  unfold tailWord_7136118
  simp only [CollatzResearch.WordTrace]
  refine ⟨16267225372566919548107063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173517070640713808513142005 16267225372566919548107063)
  ·
    refine ⟨24400838058850379322160595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16267225372566919548107063 24400838058850379322160595)
    ·
      refine ⟨36601257088275568983240893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24400838058850379322160595 36601257088275568983240893)
      ·
        refine ⟨13725471408103338368715335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36601257088275568983240893 13725471408103338368715335)
        ·
          refine ⟨20588207112155007553073003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13725471408103338368715335 20588207112155007553073003)
          ·
            refine ⟨30882310668232511329609505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20588207112155007553073003 30882310668232511329609505)
            ·
              refine ⟨23161733001174383497207129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30882310668232511329609505 23161733001174383497207129)
              ·
                refine ⟨17371299750880787622905347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23161733001174383497207129 17371299750880787622905347)
                ·
                  refine ⟨26056949626321181434358021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17371299750880787622905347 26056949626321181434358021)
                  ·
                    refine ⟨4885678054935221518942129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26056949626321181434358021 4885678054935221518942129)
                    ·
                      refine ⟨3664258541201416139206597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4885678054935221518942129 3664258541201416139206597)
                      ·
                        rfl

theorem cell23_7136118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_7136118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136118 prefixEnd_7136118 := by exact prefixLift 7136118
  have htrace : WordTrace (prefixWord ++ tailWord_7136118) baseStart_7136118 baseEnd_7136118 := by
    simpa [prefixWord, tailWord_7136118, baseEnd_7136118] using wordTrace_append hprefix tailTrace_7136118
  have hstable : (prefixWord ++ tailWord_7136118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136118).length < 2 ^ (prefixWord ++ tailWord_7136118).sum := by decide
  have hdescent : baseEnd_7136118 < baseStart_7136118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136135 : List Nat := [1, 1, 4, 2, 3, 3, 1, 2, 2, 2, 2]
def baseStart_7136135 : Nat := 118140960795 + 7136135 * 2 ^ 59
def prefixEnd_7136135 : Nat := 4983230072969 + 3 ^ 40 * 7136135 * 2
def baseEnd_7136135 : Nat := 3664267270372542572694019

theorem tailTrace_7136135 : CollatzResearch.WordTrace tailWord_7136135 prefixEnd_7136135 3664267270372542572694019 := by
  unfold tailWord_7136135
  simp only [CollatzResearch.WordTrace]
  refine ⟨260276226002009124673081859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173517484001339416448721239 260276226002009124673081859)
  ·
    refine ⟨390414339003013687009622789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260276226002009124673081859 390414339003013687009622789)
    ·
      refine ⟨73202688563065066314304273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 390414339003013687009622789 73202688563065066314304273)
      ·
        refine ⟨54902016422298799735728205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73202688563065066314304273 54902016422298799735728205)
        ·
          refine ⟨20588256158362049900898077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54902016422298799735728205 20588256158362049900898077)
          ·
            refine ⟨7720596059385768712836779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20588256158362049900898077 7720596059385768712836779)
            ·
              refine ⟨11580894089078653069255169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7720596059385768712836779 11580894089078653069255169)
              ·
                refine ⟨8685670566808989801941377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11580894089078653069255169 8685670566808989801941377)
                ·
                  refine ⟨6514252925106742351456033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8685670566808989801941377 6514252925106742351456033)
                  ·
                    refine ⟨4885689693830056763592025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6514252925106742351456033 4885689693830056763592025)
                    ·
                      refine ⟨3664267270372542572694019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4885689693830056763592025 3664267270372542572694019)
                      ·
                        rfl

theorem cell23_7136135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_7136135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136135 prefixEnd_7136135 := by exact prefixLift 7136135
  have htrace : WordTrace (prefixWord ++ tailWord_7136135) baseStart_7136135 baseEnd_7136135 := by
    simpa [prefixWord, tailWord_7136135, baseEnd_7136135] using wordTrace_append hprefix tailTrace_7136135
  have hstable : (prefixWord ++ tailWord_7136135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136135).length < 2 ^ (prefixWord ++ tailWord_7136135).sum := by decide
  have hdescent : baseEnd_7136135 < baseStart_7136135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136187 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 4]
def baseStart_7136187 : Nat := 118140960795 + 7136187 * 2 ^ 59
def prefixEnd_7136187 : Nat := 4983230072969 + 3 ^ 40 * 7136187 * 2
def baseEnd_7136187 : Nat := 3664293971366576369243779

theorem tailTrace_7136187 : CollatzResearch.WordTrace tailWord_7136187 prefixEnd_7136187 3664293971366576369243779 := by
  unfold tailWord_7136187
  simp only [CollatzResearch.WordTrace]
  refine ⟨260278122597820737553974815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173518748398547158369316543 260278122597820737553974815)
  ·
    refine ⟨390417183896731106330962223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260278122597820737553974815 390417183896731106330962223)
    ·
      refine ⟨585625775845096659496443335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390417183896731106330962223 585625775845096659496443335)
      ·
        refine ⟨878438663767644989244665003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585625775845096659496443335 878438663767644989244665003)
        ·
          refine ⟨1317657995651467483866997505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878438663767644989244665003 1317657995651467483866997505)
          ·
            refine ⟨988243496738600612900248129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1317657995651467483866997505 988243496738600612900248129)
            ·
              refine ⟨741182622553950459675186097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988243496738600612900248129 741182622553950459675186097)
              ·
                refine ⟨555886966915462844756389573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741182622553950459675186097 555886966915462844756389573)
                ·
                  refine ⟨104228806296649283391823045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 555886966915462844756389573 104228806296649283391823045)
                  ·
                    refine ⟨19542901180621740635966821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104228806296649283391823045 19542901180621740635966821)
                    ·
                      refine ⟨3664293971366576369243779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19542901180621740635966821 3664293971366576369243779)
                      ·
                        rfl

theorem cell23_7136187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 4].length) (baseStart_7136187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136187 prefixEnd_7136187 := by exact prefixLift 7136187
  have htrace : WordTrace (prefixWord ++ tailWord_7136187) baseStart_7136187 baseEnd_7136187 := by
    simpa [prefixWord, tailWord_7136187, baseEnd_7136187] using wordTrace_append hprefix tailTrace_7136187
  have hstable : (prefixWord ++ tailWord_7136187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136187).length < 2 ^ (prefixWord ++ tailWord_7136187).sum := by decide
  have hdescent : baseEnd_7136187 < baseStart_7136187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136292 : List Nat := [2, 3, 1, 4, 1, 2, 2, 3, 1, 1, 3]
def baseStart_7136292 : Nat := 118140960795 + 7136292 * 2 ^ 59
def prefixEnd_7136292 : Nat := 4983230072969 + 3 ^ 40 * 7136292 * 2
def baseEnd_7136292 : Nat := 3664347886835298458430797

theorem tailTrace_7136292 : CollatzResearch.WordTrace tailWord_7136292 prefixEnd_7136292 3664347886835298458430797 := by
  unfold tailWord_7136292
  simp only [CollatzResearch.WordTrace]
  refine ⟨130140976131220170243273565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173521301508293560324364753 130140976131220170243273565)
  ·
    refine ⟨48802866049207563841227587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130140976131220170243273565 48802866049207563841227587)
    ·
      refine ⟨73204299073811345761841381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48802866049207563841227587 73204299073811345761841381)
      ·
        refine ⟨13725806076339627330345259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73204299073811345761841381 13725806076339627330345259)
        ·
          refine ⟨20588709114509440995517889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13725806076339627330345259 20588709114509440995517889)
          ·
            refine ⟨15441531835882080746638417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20588709114509440995517889 15441531835882080746638417)
            ·
              refine ⟨11581148876911560559978813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15441531835882080746638417 11581148876911560559978813)
              ·
                refine ⟨4342930828841835209992055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11581148876911560559978813 4342930828841835209992055)
                ·
                  refine ⟨6514396243262752814988083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4342930828841835209992055 6514396243262752814988083)
                  ·
                    refine ⟨9771594364894129222482125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6514396243262752814988083 9771594364894129222482125)
                    ·
                      refine ⟨3664347886835298458430797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9771594364894129222482125 3664347886835298458430797)
                      ·
                        rfl

theorem cell23_7136292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_7136292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136292 prefixEnd_7136292 := by exact prefixLift 7136292
  have htrace : WordTrace (prefixWord ++ tailWord_7136292) baseStart_7136292 baseEnd_7136292 := by
    simpa [prefixWord, tailWord_7136292, baseEnd_7136292] using wordTrace_append hprefix tailTrace_7136292
  have hstable : (prefixWord ++ tailWord_7136292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136292).length < 2 ^ (prefixWord ++ tailWord_7136292).sum := by decide
  have hdescent : baseEnd_7136292 < baseStart_7136292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136295 : List Nat := [1, 1, 7, 1, 1, 1, 4, 1, 1, 5]
def baseStart_7136295 : Nat := 118140960795 + 7136295 * 2 ^ 59
def prefixEnd_7136295 : Nat := 4983230072969 + 3 ^ 40 * 7136295 * 2
def baseEnd_7136295 : Nat := 1221449809092420648897761

theorem tailTrace_7136295 : CollatzResearch.WordTrace tailWord_7136295 prefixEnd_7136295 1221449809092420648897761 := by
  unfold tailWord_7136295
  simp only [CollatzResearch.WordTrace]
  refine ⟨260282061681429471998906339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173521374454286314665937559 260282061681429471998906339)
  ·
    refine ⟨390423092522144207998359509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260282061681429471998906339 390423092522144207998359509)
    ·
      refine ⟨9150541230987754874961551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 390423092522144207998359509 9150541230987754874961551)
      ·
        refine ⟨13725811846481632312442327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9150541230987754874961551 13725811846481632312442327)
        ·
          refine ⟨20588717769722448468663491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13725811846481632312442327 20588717769722448468663491)
          ·
            refine ⟨30883076654583672702995237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20588717769722448468663491 30883076654583672702995237)
            ·
              refine ⟨5790576872734438631811607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30883076654583672702995237 5790576872734438631811607)
              ·
                refine ⟨8685865309101657947717411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5790576872734438631811607 8685865309101657947717411)
                ·
                  refine ⟨13028797963652486921576117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8685865309101657947717411 13028797963652486921576117)
                  ·
                    refine ⟨1221449809092420648897761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13028797963652486921576117 1221449809092420648897761)
                    ·
                      rfl

theorem cell23_7136295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_7136295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136295 prefixEnd_7136295 := by exact prefixLift 7136295
  have htrace : WordTrace (prefixWord ++ tailWord_7136295) baseStart_7136295 baseEnd_7136295 := by
    simpa [prefixWord, tailWord_7136295, baseEnd_7136295] using wordTrace_append hprefix tailTrace_7136295
  have hstable : (prefixWord ++ tailWord_7136295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136295).length < 2 ^ (prefixWord ++ tailWord_7136295).sum := by decide
  have hdescent : baseEnd_7136295 < baseStart_7136295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136318 : List Nat := [4, 2, 1, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_7136318 : Nat := 118140960795 + 7136318 * 2 ^ 59
def prefixEnd_7136318 : Nat := 4983230072969 + 3 ^ 40 * 7136318 * 2
def baseEnd_7136318 : Nat := 3664361237332315356705677

theorem tailTrace_7136318 : CollatzResearch.WordTrace tailWord_7136318 prefixEnd_7136318 3664361237332315356705677 := by
  unfold tailWord_7136318
  simp only [CollatzResearch.WordTrace]
  refine ⟨32535362570043268365874201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173521933706897431284662405 32535362570043268365874201)
  ·
    refine ⟨24401521927532451274405651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32535362570043268365874201 24401521927532451274405651)
    ·
      refine ⟨36602282891298676911608477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24401521927532451274405651 36602282891298676911608477)
      ·
        refine ⟨13725856084237003841853179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36602282891298676911608477 13725856084237003841853179)
        ·
          refine ⟨20588784126355505762779769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13725856084237003841853179 20588784126355505762779769)
          ·
            refine ⟨15441588094766629322084827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20588784126355505762779769 15441588094766629322084827)
            ·
              refine ⟨23162382142149943983127241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15441588094766629322084827 23162382142149943983127241)
              ·
                refine ⟨17371786606612457987345431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23162382142149943983127241 17371786606612457987345431)
                ·
                  refine ⟨26057679909918686981018147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17371786606612457987345431 26057679909918686981018147)
                  ·
                    refine ⟨39086519864878030471527221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26057679909918686981018147 39086519864878030471527221)
                    ·
                      refine ⟨3664361237332315356705677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39086519864878030471527221 3664361237332315356705677)
                      ·
                        rfl

theorem cell23_7136318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_7136318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136318 prefixEnd_7136318 := by exact prefixLift 7136318
  have htrace : WordTrace (prefixWord ++ tailWord_7136318) baseStart_7136318 baseEnd_7136318 := by
    simpa [prefixWord, tailWord_7136318, baseEnd_7136318] using wordTrace_append hprefix tailTrace_7136318
  have hstable : (prefixWord ++ tailWord_7136318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136318).length < 2 ^ (prefixWord ++ tailWord_7136318).sum := by decide
  have hdescent : baseEnd_7136318 < baseStart_7136318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136331 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 8, 1, 3]
def baseStart_7136331 : Nat := 118140960795 + 7136331 * 2 ^ 59
def prefixEnd_7136331 : Nat := 4983230072969 + 3 ^ 40 * 7136331 * 2
def baseEnd_7136331 : Nat := 3664367912580823805843117

theorem tailTrace_7136331 : CollatzResearch.WordTrace tailWord_7136331 prefixEnd_7136331 3664367912580823805843117 := by
  unfold tailWord_7136331
  simp only [CollatzResearch.WordTrace]
  refine ⟨260283374709299050147216847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173522249806199366764811231 260283374709299050147216847)
  ·
    refine ⟨390425062063948575220825271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260283374709299050147216847 390425062063948575220825271)
    ·
      refine ⟨585637593095922862831237907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390425062063948575220825271 585637593095922862831237907)
      ·
        refine ⟨878456389643884294246856861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585637593095922862831237907 878456389643884294246856861)
        ·
          refine ⟨329421146116456610342571323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 878456389643884294246856861 329421146116456610342571323)
          ·
            refine ⟨494131719174684915513856985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329421146116456610342571323 494131719174684915513856985)
            ·
              refine ⟨370598789381013686635392739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494131719174684915513856985 370598789381013686635392739)
              ·
                refine ⟨555898184071520529953089109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370598789381013686635392739 555898184071520529953089109)
                ·
                  refine ⟨6514431844588131210387763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 555898184071520529953089109 6514431844588131210387763)
                  ·
                    refine ⟨9771647766882196815581645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6514431844588131210387763 9771647766882196815581645)
                    ·
                      refine ⟨3664367912580823805843117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9771647766882196815581645 3664367912580823805843117)
                      ·
                        rfl

theorem cell23_7136331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 1, 3].length) (baseStart_7136331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136331 prefixEnd_7136331 := by exact prefixLift 7136331
  have htrace : WordTrace (prefixWord ++ tailWord_7136331) baseStart_7136331 baseEnd_7136331 := by
    simpa [prefixWord, tailWord_7136331, baseEnd_7136331] using wordTrace_append hprefix tailTrace_7136331
  have hstable : (prefixWord ++ tailWord_7136331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136331).length < 2 ^ (prefixWord ++ tailWord_7136331).sum := by decide
  have hdescent : baseEnd_7136331 < baseStart_7136331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136338 : List Nat := [3, 2, 2, 1, 3, 3, 2, 7]
def baseStart_7136338 : Nat := 118140960795 + 7136338 * 2 ^ 59
def prefixEnd_7136338 : Nat := 4983230072969 + 3 ^ 40 * 7136338 * 2
def baseEnd_7136338 : Nat := 135717463220200195498355

theorem tailTrace_7136338 : CollatzResearch.WordTrace tailWord_7136338 prefixEnd_7136338 135717463220200195498355 := by
  unfold tailWord_7136338
  simp only [CollatzResearch.WordTrace]
  refine ⟨65070907505068422585680417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173522420013515793561814445 65070907505068422585680417)
  ·
    refine ⟨48803180628801316939260313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65070907505068422585680417 48803180628801316939260313)
    ·
      refine ⟨36602385471600987704445235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48803180628801316939260313 36602385471600987704445235)
      ·
        refine ⟨54903578207401481556667853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36602385471600987704445235 54903578207401481556667853)
        ·
          refine ⟨20588841827775555583750445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54903578207401481556667853 20588841827775555583750445)
          ·
            refine ⟨7720815685415833343906417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20588841827775555583750445 7720815685415833343906417)
            ·
              refine ⟨5790611764061875007929813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7720815685415833343906417 5790611764061875007929813)
              ·
                refine ⟨135717463220200195498355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5790611764061875007929813 135717463220200195498355)
                ·
                  rfl

theorem cell23_7136338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 7].length) (baseStart_7136338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136338 prefixEnd_7136338 := by exact prefixLift 7136338
  have htrace : WordTrace (prefixWord ++ tailWord_7136338) baseStart_7136338 baseEnd_7136338 := by
    simpa [prefixWord, tailWord_7136338, baseEnd_7136338] using wordTrace_append hprefix tailTrace_7136338
  have hstable : (prefixWord ++ tailWord_7136338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136338).length < 2 ^ (prefixWord ++ tailWord_7136338).sum := by decide
  have hdescent : baseEnd_7136338 < baseStart_7136338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136344 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 1, 4, 5]
def baseStart_7136344 : Nat := 118140960795 + 7136344 * 2 ^ 59
def prefixEnd_7136344 : Nat := 4983230072969 + 3 ^ 40 * 7136344 * 2
def baseEnd_7136344 : Nat := 3664374587829332254980557

theorem tailTrace_7136344 : CollatzResearch.WordTrace tailWord_7136344 prefixEnd_7136344 3664374587829332254980557 := by
  unfold tailWord_7136344
  simp only [CollatzResearch.WordTrace]
  refine ⟨130141924429125976683720043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173522565905501302244960057 130141924429125976683720043)
  ·
    refine ⟨195212886643688965025580065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130141924429125976683720043 195212886643688965025580065)
    ·
      refine ⟨146409664982766723769185049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195212886643688965025580065 146409664982766723769185049)
      ·
        refine ⟨109807248737075042826888787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146409664982766723769185049 109807248737075042826888787)
        ·
          refine ⟨164710873105612564240333181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109807248737075042826888787 164710873105612564240333181)
          ·
            refine ⟨61766577414604711590124943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164710873105612564240333181 61766577414604711590124943)
            ·
              refine ⟨92649866121907067385187415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61766577414604711590124943 92649866121907067385187415)
              ·
                refine ⟨138974799182860601077781123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92649866121907067385187415 138974799182860601077781123)
                ·
                  refine ⟨208462198774290901616671685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138974799182860601077781123 208462198774290901616671685)
                  ·
                    refine ⟨39086662270179544053125941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 208462198774290901616671685 39086662270179544053125941)
                    ·
                      refine ⟨3664374587829332254980557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39086662270179544053125941 3664374587829332254980557)
                      ·
                        rfl

theorem cell23_7136344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_7136344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136344 prefixEnd_7136344 := by exact prefixLift 7136344
  have htrace : WordTrace (prefixWord ++ tailWord_7136344) baseStart_7136344 baseEnd_7136344 := by
    simpa [prefixWord, tailWord_7136344, baseEnd_7136344] using wordTrace_append hprefix tailTrace_7136344
  have hstable : (prefixWord ++ tailWord_7136344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136344).length < 2 ^ (prefixWord ++ tailWord_7136344).sum := by decide
  have hdescent : baseEnd_7136344 < baseStart_7136344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136348 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_7136348 : Nat := 118140960795 + 7136348 * 2 ^ 59
def prefixEnd_7136348 : Nat := 4983230072969 + 3 ^ 40 * 7136348 * 2
def baseEnd_7136348 : Nat := 3664376641751950239330539

theorem tailTrace_7136348 : CollatzResearch.WordTrace tailWord_7136348 prefixEnd_7136348 3664376641751950239330539 := by
  unfold tailWord_7136348
  simp only [CollatzResearch.WordTrace]
  refine ⟨130141997375118731025292849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173522663166824974700390465 130141997375118731025292849)
  ·
    refine ⟨97606498031339048268969637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130141997375118731025292849 97606498031339048268969637)
    ·
      refine ⟨18301218380876071550431807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97606498031339048268969637 18301218380876071550431807)
      ·
        refine ⟨27451827571314107325647711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18301218380876071550431807 27451827571314107325647711)
        ·
          refine ⟨41177741356971160988471567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27451827571314107325647711 41177741356971160988471567)
          ·
            refine ⟨61766612035456741482707351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41177741356971160988471567 61766612035456741482707351)
            ·
              refine ⟨92649918053185112224061027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61766612035456741482707351 92649918053185112224061027)
              ·
                refine ⟨138974877079777668336091541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92649918053185112224061027 138974877079777668336091541)
                ·
                  refine ⟨6514447363114578203254291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138974877079777668336091541 6514447363114578203254291)
                  ·
                    refine ⟨9771671044671867304881437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6514447363114578203254291 9771671044671867304881437)
                    ·
                      refine ⟨3664376641751950239330539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9771671044671867304881437 3664376641751950239330539)
                      ·
                        rfl

theorem cell23_7136348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_7136348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136348 prefixEnd_7136348 := by exact prefixLift 7136348
  have htrace : WordTrace (prefixWord ++ tailWord_7136348) baseStart_7136348 baseEnd_7136348 := by
    simpa [prefixWord, tailWord_7136348, baseEnd_7136348] using wordTrace_append hprefix tailTrace_7136348
  have hstable : (prefixWord ++ tailWord_7136348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136348).length < 2 ^ (prefixWord ++ tailWord_7136348).sum := by decide
  have hdescent : baseEnd_7136348 < baseStart_7136348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136458 : List Nat := [3, 1, 2, 1, 3, 2, 3, 1, 2, 5]
def baseStart_7136458 : Nat := 118140960795 + 7136458 * 2 ^ 59
def prefixEnd_7136458 : Nat := 4983230072969 + 3 ^ 40 * 7136458 * 2
def baseEnd_7136458 : Nat := 1221477708207981602985011

theorem tailTrace_7136458 : CollatzResearch.WordTrace tailWord_7136458 prefixEnd_7136458 1221477708207981602985011 := by
  unfold tailWord_7136458
  simp only [CollatzResearch.WordTrace]
  refine ⟨65072001694959737709272507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173525337853225967224726685 65072001694959737709272507)
  ·
    refine ⟨97608002542439606563908761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65072001694959737709272507 97608002542439606563908761)
    ·
      refine ⟨73206001906829704922931571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97608002542439606563908761 73206001906829704922931571)
      ·
        refine ⟨109809002860244557384397357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73206001906829704922931571 109809002860244557384397357)
        ·
          refine ⟨41178376072591709019149009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109809002860244557384397357 41178376072591709019149009)
          ·
            refine ⟨30883782054443781764361757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41178376072591709019149009 30883782054443781764361757)
            ·
              refine ⟨11581418270416418161635659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30883782054443781764361757 11581418270416418161635659)
              ·
                refine ⟨17372127405624627242453489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11581418270416418161635659 17372127405624627242453489)
                ·
                  refine ⟨13029095554218470431840117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17372127405624627242453489 13029095554218470431840117)
                  ·
                    refine ⟨1221477708207981602985011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13029095554218470431840117 1221477708207981602985011)
                    ·
                      rfl

theorem cell23_7136458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_7136458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136458 prefixEnd_7136458 := by exact prefixLift 7136458
  have htrace : WordTrace (prefixWord ++ tailWord_7136458) baseStart_7136458 baseEnd_7136458 := by
    simpa [prefixWord, tailWord_7136458, baseEnd_7136458] using wordTrace_append hprefix tailTrace_7136458
  have hstable : (prefixWord ++ tailWord_7136458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136458).length < 2 ^ (prefixWord ++ tailWord_7136458).sum := by decide
  have hdescent : baseEnd_7136458 < baseStart_7136458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136531 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 7, 5]
def baseStart_7136531 : Nat := 118140960795 + 7136531 * 2 ^ 59
def prefixEnd_7136531 : Nat := 4983230072969 + 3 ^ 40 * 7136531 * 2
def baseEnd_7136531 : Nat := 1221490202903907674447399

theorem tailTrace_7136531 : CollatzResearch.WordTrace tailWord_7136531 prefixEnd_7136531 1221490202903907674447399 := by
  unfold tailWord_7136531
  simp only [CollatzResearch.WordTrace]
  refine ⟨260290669308574484304497447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173527112872382989536331631 260290669308574484304497447)
  ·
    refine ⟨390436003962861726456746171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260290669308574484304497447 390436003962861726456746171)
    ·
      refine ⟨585654005944292589685119257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390436003962861726456746171 585654005944292589685119257)
      ·
        refine ⟨439240504458219442263839443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585654005944292589685119257 439240504458219442263839443)
        ·
          refine ⟨658860756687329163395759165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439240504458219442263839443 658860756687329163395759165)
          ·
            refine ⟨247072783757748436273409687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 658860756687329163395759165 247072783757748436273409687)
            ·
              refine ⟨370609175636622654410114531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247072783757748436273409687 370609175636622654410114531)
              ·
                refine ⟨555913763454933981615171797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370609175636622654410114531 555913763454933981615171797)
                ·
                  refine ⟨13029228830975015194105589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 555913763454933981615171797 13029228830975015194105589)
                  ·
                    refine ⟨1221490202903907674447399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13029228830975015194105589 1221490202903907674447399)
                    ·
                      rfl

theorem cell23_7136531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 5].length) (baseStart_7136531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136531 prefixEnd_7136531 := by exact prefixLift 7136531
  have htrace : WordTrace (prefixWord ++ tailWord_7136531) baseStart_7136531 baseEnd_7136531 := by
    simpa [prefixWord, tailWord_7136531, baseEnd_7136531] using wordTrace_append hprefix tailTrace_7136531
  have hstable : (prefixWord ++ tailWord_7136531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136531).length < 2 ^ (prefixWord ++ tailWord_7136531).sum := by decide
  have hdescent : baseEnd_7136531 < baseStart_7136531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136548 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 3, 5]
def baseStart_7136548 : Nat := 118140960795 + 7136548 * 2 ^ 59
def prefixEnd_7136548 : Nat := 4983230072969 + 3 ^ 40 * 7136548 * 2
def baseEnd_7136548 : Nat := 1221493112627616485609873

theorem tailTrace_7136548 : CollatzResearch.WordTrace tailWord_7136548 prefixEnd_7136548 1221493112627616485609873 := by
  unfold tailWord_7136548
  simp only [CollatzResearch.WordTrace]
  refine ⟨130145644674756448103933149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173527526233008597471910865 130145644674756448103933149)
  ·
    refine ⟨48804616753033668038974931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130145644674756448103933149 48804616753033668038974931)
    ·
      refine ⟨73206925129550502058462397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48804616753033668038974931 73206925129550502058462397)
      ·
        refine ⟨27452596923581438271923399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73206925129550502058462397 27452596923581438271923399)
        ·
          refine ⟨41178895385372157407885099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27452596923581438271923399 41178895385372157407885099)
          ·
            refine ⟨61768343078058236111827649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41178895385372157407885099 61768343078058236111827649)
            ·
              refine ⟨46326257308543677083870737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61768343078058236111827649 46326257308543677083870737)
              ·
                refine ⟨34744692981407757812903053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46326257308543677083870737 34744692981407757812903053)
                ·
                  refine ⟨13029259868027909179838645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34744692981407757812903053 13029259868027909179838645)
                  ·
                    refine ⟨1221493112627616485609873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13029259868027909179838645 1221493112627616485609873)
                    ·
                      rfl

theorem cell23_7136548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_7136548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136548 prefixEnd_7136548 := by exact prefixLift 7136548
  have htrace : WordTrace (prefixWord ++ tailWord_7136548) baseStart_7136548 baseEnd_7136548 := by
    simpa [prefixWord, tailWord_7136548, baseEnd_7136548] using wordTrace_append hprefix tailTrace_7136548
  have hstable : (prefixWord ++ tailWord_7136548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136548).length < 2 ^ (prefixWord ++ tailWord_7136548).sum := by decide
  have hdescent : baseEnd_7136548 < baseStart_7136548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136552 : List Nat := [2, 1, 5, 1, 2, 3, 2, 1, 6]
def baseStart_7136552 : Nat := 118140960795 + 7136552 * 2 ^ 59
def prefixEnd_7136552 : Nat := 4983230072969 + 3 ^ 40 * 7136552 * 2
def baseEnd_7136552 : Nat := 407164599089496382353289

theorem tailTrace_7136552 : CollatzResearch.WordTrace tailWord_7136552 prefixEnd_7136552 407164599089496382353289 := by
  unfold tailWord_7136552
  simp only [CollatzResearch.WordTrace]
  refine ⟨130145717620749202445505955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173527623494332269927341273 130145717620749202445505955)
  ·
    refine ⟨195218576431123803668258933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130145717620749202445505955 195218576431123803668258933)
    ·
      refine ⟨18301741540417856593899275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195218576431123803668258933 18301741540417856593899275)
      ·
        refine ⟨27452612310626784890848913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18301741540417856593899275 27452612310626784890848913)
        ·
          refine ⟨20589459232970088668136685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27452612310626784890848913 20589459232970088668136685)
          ·
            refine ⟨7721047212363783250551257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20589459232970088668136685 7721047212363783250551257)
            ·
              refine ⟨5790785409272837437913443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7721047212363783250551257 5790785409272837437913443)
              ·
                refine ⟨8686178113909256156870165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5790785409272837437913443 8686178113909256156870165)
                ·
                  refine ⟨407164599089496382353289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8686178113909256156870165 407164599089496382353289)
                  ·
                    rfl

theorem cell23_7136552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 6].length) (baseStart_7136552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136552 prefixEnd_7136552 := by exact prefixLift 7136552
  have htrace : WordTrace (prefixWord ++ tailWord_7136552) baseStart_7136552 baseEnd_7136552 := by
    simpa [prefixWord, tailWord_7136552, baseEnd_7136552] using wordTrace_append hprefix tailTrace_7136552
  have hstable : (prefixWord ++ tailWord_7136552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136552).length < 2 ^ (prefixWord ++ tailWord_7136552).sum := by decide
  have hdescent : baseEnd_7136552 < baseStart_7136552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136565 : List Nat := [1, 3, 3, 1, 2, 2, 3, 2, 1, 5]
def baseStart_7136565 : Nat := 118140960795 + 7136565 * 2 ^ 59
def prefixEnd_7136565 : Nat := 4983230072969 + 3 ^ 40 * 7136565 * 2
def baseEnd_7136565 : Nat := 1221496022351325296772347

theorem tailTrace_7136565 : CollatzResearch.WordTrace tailWord_7136565 prefixEnd_7136565 1221496022351325296772347 := by
  unfold tailWord_7136565
  simp only [CollatzResearch.WordTrace]
  refine ⟨260291909390451308111235149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173527939593634205407490099 260291909390451308111235149)
  ·
    refine ⟨97609466021419240541713181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260291909390451308111235149 97609466021419240541713181)
    ·
      refine ⟨36603549758032215203142443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97609466021419240541713181 36603549758032215203142443)
      ·
        refine ⟨54905324637048322804713665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36603549758032215203142443 54905324637048322804713665)
        ·
          refine ⟨41178993477786242103535249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54905324637048322804713665 41178993477786242103535249)
          ·
            refine ⟨30884245108339681577651437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41178993477786242103535249 30884245108339681577651437)
            ·
              refine ⟨11581591915627380591619289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30884245108339681577651437 11581591915627380591619289)
              ·
                refine ⟨8686193936720535443714467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11581591915627380591619289 8686193936720535443714467)
                ·
                  refine ⟨13029290905080803165571701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8686193936720535443714467 13029290905080803165571701)
                  ·
                    refine ⟨1221496022351325296772347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13029290905080803165571701 1221496022351325296772347)
                    ·
                      rfl

theorem cell23_7136565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_7136565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136565 prefixEnd_7136565 := by exact prefixLift 7136565
  have htrace : WordTrace (prefixWord ++ tailWord_7136565) baseStart_7136565 baseEnd_7136565 := by
    simpa [prefixWord, tailWord_7136565, baseEnd_7136565] using wordTrace_append hprefix tailTrace_7136565
  have hstable : (prefixWord ++ tailWord_7136565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136565).length < 2 ^ (prefixWord ++ tailWord_7136565).sum := by decide
  have hdescent : baseEnd_7136565 < baseStart_7136565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136572 : List Nat := [2, 2, 2, 2, 1, 4, 2, 1, 2, 3, 2]
def baseStart_7136572 : Nat := 118140960795 + 7136572 * 2 ^ 59
def prefixEnd_7136572 : Nat := 4983230072969 + 3 ^ 40 * 7136572 * 2
def baseEnd_7136572 : Nat := 3664491661418557362929509

theorem tailTrace_7136572 : CollatzResearch.WordTrace tailWord_7136572 prefixEnd_7136572 3664491661418557362929509 := by
  unfold tailWord_7136572
  simp only [CollatzResearch.WordTrace]
  refine ⟨130146082350712974153369985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173528109800950632204493313 130146082350712974153369985)
  ·
    refine ⟨97609561763034730615027489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130146082350712974153369985 97609561763034730615027489)
    ·
      refine ⟨73207171322276047961270617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97609561763034730615027489 73207171322276047961270617)
      ·
        refine ⟨54905378491707035970952963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73207171322276047961270617 54905378491707035970952963)
        ·
          refine ⟨82358067737560553956429445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54905378491707035970952963 82358067737560553956429445)
          ·
            refine ⟨15442137700792603866830521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82358067737560553956429445 15442137700792603866830521)
            ·
              refine ⟨11581603275594452900122891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15442137700792603866830521 11581603275594452900122891)
              ·
                refine ⟨17372404913391679350184337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11581603275594452900122891 17372404913391679350184337)
                ·
                  refine ⟨13029303685043759512638253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17372404913391679350184337 13029303685043759512638253)
                  ·
                    refine ⟨4885988881891409817239345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13029303685043759512638253 4885988881891409817239345)
                    ·
                      refine ⟨3664491661418557362929509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4885988881891409817239345 3664491661418557362929509)
                      ·
                        rfl

theorem cell23_7136572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_7136572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136572 prefixEnd_7136572 := by exact prefixLift 7136572
  have htrace : WordTrace (prefixWord ++ tailWord_7136572) baseStart_7136572 baseEnd_7136572 := by
    simpa [prefixWord, tailWord_7136572, baseEnd_7136572] using wordTrace_append hprefix tailTrace_7136572
  have hstable : (prefixWord ++ tailWord_7136572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136572).length < 2 ^ (prefixWord ++ tailWord_7136572).sum := by decide
  have hdescent : baseEnd_7136572 < baseStart_7136572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136595 : List Nat := [1, 1, 1, 2, 1, 1, 8, 2, 2, 4]
def baseStart_7136595 : Nat := 118140960795 + 7136595 * 2 ^ 59
def prefixEnd_7136595 : Nat := 4983230072969 + 3 ^ 40 * 7136595 * 2
def baseEnd_7136595 : Nat := 1221501157157870257647301

theorem tailTrace_7136595 : CollatzResearch.WordTrace tailWord_7136595 prefixEnd_7136595 1221501157157870257647301 := by
  unfold tailWord_7136595
  simp only [CollatzResearch.WordTrace]
  refine ⟨260293003580342623234827239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173528669053561748823218159 260293003580342623234827239)
  ·
    refine ⟨390439505370513934852240859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260293003580342623234827239 390439505370513934852240859)
    ·
      refine ⟨585659258055770902278361289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390439505370513934852240859 585659258055770902278361289)
      ·
        refine ⟨439244443541828176708770967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585659258055770902278361289 439244443541828176708770967)
        ·
          refine ⟨658866665312742265063156451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439244443541828176708770967 658866665312742265063156451)
          ·
            refine ⟨988299997969113397594734677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658866665312742265063156451 988299997969113397594734677)
            ·
              refine ⟨11581640601200547628063297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 988299997969113397594734677 11581640601200547628063297)
              ·
                refine ⟨8686230450900410721047473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11581640601200547628063297 8686230450900410721047473)
                ·
                  refine ⟨6514672838175308040785605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8686230450900410721047473 6514672838175308040785605)
                  ·
                    refine ⟨1221501157157870257647301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6514672838175308040785605 1221501157157870257647301)
                    ·
                      rfl

theorem cell23_7136595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 4].length) (baseStart_7136595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136595 prefixEnd_7136595 := by exact prefixLift 7136595
  have htrace : WordTrace (prefixWord ++ tailWord_7136595) baseStart_7136595 baseEnd_7136595 := by
    simpa [prefixWord, tailWord_7136595, baseEnd_7136595] using wordTrace_append hprefix tailTrace_7136595
  have hstable : (prefixWord ++ tailWord_7136595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136595).length < 2 ^ (prefixWord ++ tailWord_7136595).sum := by decide
  have hdescent : baseEnd_7136595 < baseStart_7136595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136608 : List Nat := [2, 1, 1, 3, 4, 1, 3, 8]
def baseStart_7136608 : Nat := 118140960795 + 7136608 * 2 ^ 59
def prefixEnd_7136608 : Nat := 4983230072969 + 3 ^ 40 * 7136608 * 2
def baseEnd_7136608 : Nat := 135722598026745156373309

theorem tailTrace_7136608 : CollatzResearch.WordTrace tailWord_7136608 prefixEnd_7136608 135722598026745156373309 := by
  unfold tailWord_7136608
  simp only [CollatzResearch.WordTrace]
  refine ⟨130146738864647763227525239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173528985152863684303366985 130146738864647763227525239)
  ·
    refine ⟨195220108296971644841287859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130146738864647763227525239 195220108296971644841287859)
    ·
      refine ⟨292830162445457467261931789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195220108296971644841287859 292830162445457467261931789)
      ·
        refine ⟨109811310917046550223224421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292830162445457467261931789 109811310917046550223224421)
        ·
          refine ⟨20589620796946228166854579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109811310917046550223224421 20589620796946228166854579)
          ·
            refine ⟨30884431195419342250281869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20589620796946228166854579 30884431195419342250281869)
            ·
              refine ⟨11581661698282253343855701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30884431195419342250281869 11581661698282253343855701)
              ·
                refine ⟨135722598026745156373309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11581661698282253343855701 135722598026745156373309)
                ·
                  rfl

theorem cell23_7136608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 8].length) (baseStart_7136608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136608 prefixEnd_7136608 := by exact prefixLift 7136608
  have htrace : WordTrace (prefixWord ++ tailWord_7136608) baseStart_7136608 baseEnd_7136608 := by
    simpa [prefixWord, tailWord_7136608, baseEnd_7136608] using wordTrace_append hprefix tailTrace_7136608
  have hstable : (prefixWord ++ tailWord_7136608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136608).length < 2 ^ (prefixWord ++ tailWord_7136608).sum := by decide
  have hdescent : baseEnd_7136608 < baseStart_7136608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136635 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 4, 1, 3]
def baseStart_7136635 : Nat := 118140960795 + 7136635 * 2 ^ 59
def prefixEnd_7136635 : Nat := 4983230072969 + 3 ^ 40 * 7136635 * 2
def baseEnd_7136635 : Nat := 3664524010699790616441719

theorem tailTrace_7136635 : CollatzResearch.WordTrace tailWord_7136635 prefixEnd_7136635 3664524010699790616441719 := by
  unfold tailWord_7136635
  simp only [CollatzResearch.WordTrace]
  refine ⟨260294462500197710066283359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173529641666798473377522239 260294462500197710066283359)
  ·
    refine ⟨390441693750296565099425039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260294462500197710066283359 390441693750296565099425039)
    ·
      refine ⟨585662540625444847649137559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390441693750296565099425039 585662540625444847649137559)
      ·
        refine ⟨878493810938167271473706339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585662540625444847649137559 878493810938167271473706339)
        ·
          refine ⟨1317740716407250907210559509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878493810938167271473706339 1317740716407250907210559509)
          ·
            refine ⟨61769096081589886275494977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1317740716407250907210559509 61769096081589886275494977)
            ·
              refine ⟨46326822061192414706621233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61769096081589886275494977 46326822061192414706621233)
              ·
                refine ⟨34745116545894311029965925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46326822061192414706621233 34745116545894311029965925)
                ·
                  refine ⟨6514709352355183318118611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34745116545894311029965925 6514709352355183318118611)
                  ·
                    refine ⟨9772064028532774977177917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6514709352355183318118611 9772064028532774977177917)
                    ·
                      refine ⟨3664524010699790616441719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9772064028532774977177917 3664524010699790616441719)
                      ·
                        rfl

theorem cell23_7136635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 1, 3].length) (baseStart_7136635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136635 prefixEnd_7136635 := by exact prefixLift 7136635
  have htrace : WordTrace (prefixWord ++ tailWord_7136635) baseStart_7136635 baseEnd_7136635 := by
    simpa [prefixWord, tailWord_7136635, baseEnd_7136635] using wordTrace_append hprefix tailTrace_7136635
  have hstable : (prefixWord ++ tailWord_7136635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136635).length < 2 ^ (prefixWord ++ tailWord_7136635).sum := by decide
  have hdescent : baseEnd_7136635 < baseStart_7136635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136679 : List Nat := [1, 1, 6, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_7136679 : Nat := 118140960795 + 7136679 * 2 ^ 59
def prefixEnd_7136679 : Nat := 4983230072969 + 3 ^ 40 * 7136679 * 2
def baseEnd_7136679 : Nat := 3664546603848588444291517

theorem tailTrace_7136679 : CollatzResearch.WordTrace tailWord_7136679 prefixEnd_7136679 3664546603848588444291517 := by
  unfold tailWord_7136679
  simp only [CollatzResearch.WordTrace]
  refine ⟨260296067312038305580885091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173530711541358870387256727 260296067312038305580885091)
  ·
    refine ⟨390444100968057458371327637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260296067312038305580885091 390444100968057458371327637)
    ·
      refine ⟨18302067232877693361155983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 390444100968057458371327637 18302067232877693361155983)
      ·
        refine ⟨27453100849316540041733975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18302067232877693361155983 27453100849316540041733975)
        ·
          refine ⟨41179651273974810062600963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27453100849316540041733975 41179651273974810062600963)
          ·
            refine ⟨61769476910962215093901445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41179651273974810062600963 61769476910962215093901445)
            ·
              refine ⟨11581776920805415330106521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61769476910962215093901445 11581776920805415330106521)
              ·
                refine ⟨8686332690604061497579891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11581776920805415330106521 8686332690604061497579891)
                ·
                  refine ⟨13029499035906092246369837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8686332690604061497579891 13029499035906092246369837)
                  ·
                    refine ⟨4886062138464784592388689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13029499035906092246369837 4886062138464784592388689)
                    ·
                      refine ⟨3664546603848588444291517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4886062138464784592388689 3664546603848588444291517)
                      ·
                        rfl

theorem cell23_7136679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_7136679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136679 prefixEnd_7136679 := by exact prefixLift 7136679
  have htrace : WordTrace (prefixWord ++ tailWord_7136679) baseStart_7136679 baseEnd_7136679 := by
    simpa [prefixWord, tailWord_7136679, baseEnd_7136679] using wordTrace_append hprefix tailTrace_7136679
  have hstable : (prefixWord ++ tailWord_7136679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136679).length < 2 ^ (prefixWord ++ tailWord_7136679).sum := by decide
  have hdescent : baseEnd_7136679 < baseStart_7136679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136688 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 4]
def baseStart_7136688 : Nat := 118140960795 + 7136688 * 2 ^ 59
def prefixEnd_7136688 : Nat := 4983230072969 + 3 ^ 40 * 7136688 * 2
def baseEnd_7136688 : Nat := 3664551225174478909078975

theorem tailTrace_7136688 : CollatzResearch.WordTrace tailWord_7136688 prefixEnd_7136688 3664551225174478909078975 := by
  unfold tailWord_7136688
  simp only [CollatzResearch.WordTrace]
  refine ⟨130148197784502850058981359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173530930379337133411975145 130148197784502850058981359)
  ·
    refine ⟨195222296676754275088472039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130148197784502850058981359 195222296676754275088472039)
    ·
      refine ⟨292833445015131412632708059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195222296676754275088472039 292833445015131412632708059)
      ·
        refine ⟨439250167522697118949062089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292833445015131412632708059 439250167522697118949062089)
        ·
          refine ⟨329437625642022839211796567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439250167522697118949062089 329437625642022839211796567)
          ·
            refine ⟨494156438463034258817694851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329437625642022839211796567 494156438463034258817694851)
            ·
              refine ⟨741234657694551388226542277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494156438463034258817694851 741234657694551388226542277)
              ·
                refine ⟨138981498317728385292476677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 741234657694551388226542277 138981498317728385292476677)
                ·
                  refine ⟨26059030934574072242339377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138981498317728385292476677 26059030934574072242339377)
                  ·
                    refine ⟨19544273200930554181754533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26059030934574072242339377 19544273200930554181754533)
                    ·
                      refine ⟨3664551225174478909078975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19544273200930554181754533 3664551225174478909078975)
                      ·
                        rfl

theorem cell23_7136688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_7136688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136688 prefixEnd_7136688 := by exact prefixLift 7136688
  have htrace : WordTrace (prefixWord ++ tailWord_7136688) baseStart_7136688 baseEnd_7136688 := by
    simpa [prefixWord, tailWord_7136688, baseEnd_7136688] using wordTrace_append hprefix tailTrace_7136688
  have hstable : (prefixWord ++ tailWord_7136688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136688).length < 2 ^ (prefixWord ++ tailWord_7136688).sum := by decide
  have hdescent : baseEnd_7136688 < baseStart_7136688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136715 : List Nat := [1, 1, 1, 1, 3, 3, 2, 6, 5]
def baseStart_7136715 : Nat := 118140960795 + 7136715 * 2 ^ 59
def prefixEnd_7136715 : Nat := 4983230072969 + 3 ^ 40 * 7136715 * 2
def baseEnd_7136715 : Nat := 407173898794683367049039

theorem tailTrace_7136715 : CollatzResearch.WordTrace tailWord_7136715 prefixEnd_7136715 407173898794683367049039 := by
  unfold tailWord_7136715
  simp only [CollatzResearch.WordTrace]
  refine ⟨260297380339907883729195599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173531586893271922486130399 260297380339907883729195599)
  ·
    refine ⟨390446070509861825593793399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260297380339907883729195599 390446070509861825593793399)
    ·
      refine ⟨585669105764792738390690099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390446070509861825593793399 585669105764792738390690099)
      ·
        refine ⟨878503658647189107586035149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585669105764792738390690099 878503658647189107586035149)
        ·
          refine ⟨329438871992695915344763181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 878503658647189107586035149 329438871992695915344763181)
          ·
            refine ⟨123539576997260968254286193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329438871992695915344763181 123539576997260968254286193)
            ·
              refine ⟨92654682747945726190714645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123539576997260968254286193 92654682747945726190714645)
              ·
                refine ⟨4343188253809955915189749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92654682747945726190714645 4343188253809955915189749)
                ·
                  refine ⟨407173898794683367049039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4343188253809955915189749 407173898794683367049039)
                  ·
                    rfl

theorem cell23_7136715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 5].length) (baseStart_7136715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136715 prefixEnd_7136715 := by exact prefixLift 7136715
  have htrace : WordTrace (prefixWord ++ tailWord_7136715) baseStart_7136715 baseEnd_7136715 := by
    simpa [prefixWord, tailWord_7136715, baseEnd_7136715] using wordTrace_append hprefix tailTrace_7136715
  have hstable : (prefixWord ++ tailWord_7136715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136715).length < 2 ^ (prefixWord ++ tailWord_7136715).sum := by decide
  have hdescent : baseEnd_7136715 < baseStart_7136715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136725 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 1, 5, 3]
def baseStart_7136725 : Nat := 118140960795 + 7136725 * 2 ^ 59
def prefixEnd_7136725 : Nat := 4983230072969 + 3 ^ 40 * 7136725 * 2
def baseEnd_7136725 : Nat := 3664570223958695264316305

theorem tailTrace_7136725 : CollatzResearch.WordTrace tailWord_7136725 prefixEnd_7136725 3664570223958695264316305 := by
  unfold tailWord_7136725
  simp only [CollatzResearch.WordTrace]
  refine ⟨260297745069871655437059629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173531830046581103624706419 260297745069871655437059629)
  ·
    refine ⟨97611654401201870788897361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260297745069871655437059629 97611654401201870788897361)
    ·
      refine ⟨73208740800901403091673021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97611654401201870788897361 73208740800901403091673021)
      ·
        refine ⟨27453277800338026159377383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73208740800901403091673021 27453277800338026159377383)
        ·
          refine ⟨41179916700507039239066075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27453277800338026159377383 41179916700507039239066075)
          ·
            refine ⟨61769875050760558858599113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41179916700507039239066075 61769875050760558858599113)
            ·
              refine ⟨46327406288070419143949335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61769875050760558858599113 46327406288070419143949335)
              ·
                refine ⟨69491109432105628715924003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46327406288070419143949335 69491109432105628715924003)
                ·
                  refine ⟨104236664148158443073886005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69491109432105628715924003 104236664148158443073886005)
                  ·
                    refine ⟨9772187263889854038176813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104236664148158443073886005 9772187263889854038176813)
                    ·
                      refine ⟨3664570223958695264316305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9772187263889854038176813 3664570223958695264316305)
                      ·
                        rfl

theorem cell23_7136725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_7136725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136725 prefixEnd_7136725 := by exact prefixLift 7136725
  have htrace : WordTrace (prefixWord ++ tailWord_7136725) baseStart_7136725 baseEnd_7136725 := by
    simpa [prefixWord, tailWord_7136725, baseEnd_7136725] using wordTrace_append hprefix tailTrace_7136725
  have hstable : (prefixWord ++ tailWord_7136725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136725).length < 2 ^ (prefixWord ++ tailWord_7136725).sum := by decide
  have hdescent : baseEnd_7136725 < baseStart_7136725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136728 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 3, 7]
def baseStart_7136728 : Nat := 118140960795 + 7136728 * 2 ^ 59
def prefixEnd_7136728 : Nat := 4983230072969 + 3 ^ 40 * 7136728 * 2
def baseEnd_7136728 : Nat := 1221523921466886250859597

theorem tailTrace_7136728 : CollatzResearch.WordTrace tailWord_7136728 prefixEnd_7136728 1221523921466886250859597 := by
  unfold tailWord_7136728
  simp only [CollatzResearch.WordTrace]
  refine ⟨130148927244430393474709419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173531902992573857966279225 130148927244430393474709419)
  ·
    refine ⟨195223390866645590212064129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130148927244430393474709419 195223390866645590212064129)
    ·
      refine ⟨146417543149984192659048097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195223390866645590212064129 146417543149984192659048097)
      ·
        refine ⟨109813157362488144494286073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146417543149984192659048097 109813157362488144494286073)
        ·
          refine ⟨82359868021866108370714555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109813157362488144494286073 82359868021866108370714555)
          ·
            refine ⟨123539802032799162556071833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82359868021866108370714555 123539802032799162556071833)
            ·
              refine ⟨92654851524599371917053875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123539802032799162556071833 92654851524599371917053875)
              ·
                refine ⟨138982277286899057875580813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92654851524599371917053875 138982277286899057875580813)
                ·
                  refine ⟨52118353982587146703342805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138982277286899057875580813 52118353982587146703342805)
                  ·
                    refine ⟨1221523921466886250859597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52118353982587146703342805 1221523921466886250859597)
                    ·
                      rfl

theorem cell23_7136728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_7136728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136728 prefixEnd_7136728 := by exact prefixLift 7136728
  have htrace : WordTrace (prefixWord ++ tailWord_7136728) baseStart_7136728 baseEnd_7136728 := by
    simpa [prefixWord, tailWord_7136728, baseEnd_7136728] using wordTrace_append hprefix tailTrace_7136728
  have hstable : (prefixWord ++ tailWord_7136728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136728).length < 2 ^ (prefixWord ++ tailWord_7136728).sum := by decide
  have hdescent : baseEnd_7136728 < baseStart_7136728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136766 : List Nat := [4, 2, 2, 3, 1, 1, 1, 4, 5]
def baseStart_7136766 : Nat := 118140960795 + 7136766 * 2 ^ 59
def prefixEnd_7136766 : Nat := 4983230072969 + 3 ^ 40 * 7136766 * 2
def baseEnd_7136766 : Nat := 407176808518392178211513

theorem tailTrace_7136766 : CollatzResearch.WordTrace tailWord_7136766 prefixEnd_7136766 407176808518392178211513 := by
  unfold tailWord_7136766
  simp only [CollatzResearch.WordTrace]
  refine ⟨32537405057840389929912769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173532826975148746292868101 32537405057840389929912769)
  ·
    refine ⟨24403053793380292447434577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32537405057840389929912769 24403053793380292447434577)
    ·
      refine ⟨18302290345035219335575933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24403053793380292447434577 18302290345035219335575933)
      ·
        refine ⟨6863358879388207250840975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18302290345035219335575933 6863358879388207250840975)
        ·
          refine ⟨10295038319082310876261463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6863358879388207250840975 10295038319082310876261463)
          ·
            refine ⟨15442557478623466314392195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10295038319082310876261463 15442557478623466314392195)
            ·
              refine ⟨23163836217935199471588293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15442557478623466314392195 23163836217935199471588293)
              ·
                refine ⟨4343219290862849900922805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23163836217935199471588293 4343219290862849900922805)
                ·
                  refine ⟨407176808518392178211513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4343219290862849900922805 407176808518392178211513)
                  ·
                    rfl

theorem cell23_7136766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_7136766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136766 prefixEnd_7136766 := by exact prefixLift 7136766
  have htrace : WordTrace (prefixWord ++ tailWord_7136766) baseStart_7136766 baseEnd_7136766 := by
    simpa [prefixWord, tailWord_7136766, baseEnd_7136766] using wordTrace_append hprefix tailTrace_7136766
  have hstable : (prefixWord ++ tailWord_7136766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136766).length < 2 ^ (prefixWord ++ tailWord_7136766).sum := by decide
  have hdescent : baseEnd_7136766 < baseStart_7136766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136785 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 3]
def baseStart_7136785 : Nat := 118140960795 + 7136785 * 2 ^ 59
def prefixEnd_7136785 : Nat := 4983230072969 + 3 ^ 40 * 7136785 * 2
def baseEnd_7136785 : Nat := 3664601032797965029566029

theorem tailTrace_7136785 : CollatzResearch.WordTrace tailWord_7136785 prefixEnd_7136785 3664601032797965029566029 := by
  unfold tailWord_7136785
  simp only [CollatzResearch.WordTrace]
  refine ⟨260299933449654285684243809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173533288966436190456162539 260299933449654285684243809)
  ·
    refine ⟨195224950087240714263182857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260299933449654285684243809 195224950087240714263182857)
    ·
      refine ⟨146418712565430535697387143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195224950087240714263182857 146418712565430535697387143)
      ·
        refine ⟨219628068848145803546080715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146418712565430535697387143 219628068848145803546080715)
        ·
          refine ⟨329442103272218705319121073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219628068848145803546080715 329442103272218705319121073)
          ·
            refine ⟨247081577454164028989340805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329442103272218705319121073 247081577454164028989340805)
            ·
              refine ⟨46327795772655755435501401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247081577454164028989340805 46327795772655755435501401)
              ·
                refine ⟨34745846829491816576626051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46327795772655755435501401 34745846829491816576626051)
                ·
                  refine ⟨52118770244237724864939077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34745846829491816576626051 52118770244237724864939077)
                  ·
                    refine ⟨9772269420794573412176077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52118770244237724864939077 9772269420794573412176077)
                    ·
                      refine ⟨3664601032797965029566029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9772269420794573412176077 3664601032797965029566029)
                      ·
                        rfl

theorem cell23_7136785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_7136785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136785 prefixEnd_7136785 := by exact prefixLift 7136785
  have htrace : WordTrace (prefixWord ++ tailWord_7136785) baseStart_7136785 baseEnd_7136785 := by
    simpa [prefixWord, tailWord_7136785, baseEnd_7136785] using wordTrace_append hprefix tailTrace_7136785
  have hstable : (prefixWord ++ tailWord_7136785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136785).length < 2 ^ (prefixWord ++ tailWord_7136785).sum := by decide
  have hdescent : baseEnd_7136785 < baseStart_7136785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136825 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 1, 2, 6]
def baseStart_7136825 : Nat := 118140960795 + 7136825 * 2 ^ 59
def prefixEnd_7136825 : Nat := 4983230072969 + 3 ^ 40 * 7136825 * 2
def baseEnd_7136825 : Nat := 3664621572024144873065845

theorem tailTrace_7136825 : CollatzResearch.WordTrace tailWord_7136825 prefixEnd_7136825 3664621572024144873065845 := by
  unfold tailWord_7136825
  simp only [CollatzResearch.WordTrace]
  refine ⟨260301392369509372515699929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173534261579672915010466619 260301392369509372515699929)
  ·
    refine ⟨195226044277132029386774947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260301392369509372515699929 195226044277132029386774947)
    ·
      refine ⟨292839066415698044080162421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195226044277132029386774947 292839066415698044080162421)
      ·
        refine ⟨27453662476471691632515227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 292839066415698044080162421 27453662476471691632515227)
        ·
          refine ⟨41180493714707537448772841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27453662476471691632515227 41180493714707537448772841)
          ·
            refine ⟨30885370286030653086579631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41180493714707537448772841 30885370286030653086579631)
            ·
              refine ⟨46328055429045979629869447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30885370286030653086579631 46328055429045979629869447)
              ·
                refine ⟨69492083143568969444804171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46328055429045979629869447 69492083143568969444804171)
                ·
                  refine ⟨104238124715353454167206257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69492083143568969444804171 104238124715353454167206257)
                  ·
                    refine ⟨78178593536515090625404693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104238124715353454167206257 78178593536515090625404693)
                    ·
                      refine ⟨3664621572024144873065845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78178593536515090625404693 3664621572024144873065845)
                      ·
                        rfl

theorem cell23_7136825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_7136825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136825 prefixEnd_7136825 := by exact prefixLift 7136825
  have htrace : WordTrace (prefixWord ++ tailWord_7136825) baseStart_7136825 baseEnd_7136825 := by
    simpa [prefixWord, tailWord_7136825, baseEnd_7136825] using wordTrace_append hprefix tailTrace_7136825
  have hstable : (prefixWord ++ tailWord_7136825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136825).length < 2 ^ (prefixWord ++ tailWord_7136825).sum := by decide
  have hdescent : baseEnd_7136825 < baseStart_7136825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136839 : List Nat := [1, 1, 4, 1, 5, 1, 3, 1, 6]
def baseStart_7136839 : Nat := 118140960795 + 7136839 * 2 ^ 59
def prefixEnd_7136839 : Nat := 4983230072969 + 3 ^ 40 * 7136839 * 2
def baseEnd_7136839 : Nat := 407180973417034202032309

theorem tailTrace_7136839 : CollatzResearch.WordTrace tailWord_7136839 prefixEnd_7136839 407180973417034202032309 := by
  unfold tailWord_7136839
  simp only [CollatzResearch.WordTrace]
  refine ⟨260301902991458652906709571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173534601994305768604473047 260301902991458652906709571)
  ·
    refine ⟨390452854487187979360064357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260301902991458652906709571 390452854487187979360064357)
    ·
      refine ⟨73209910216347746130012067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 390452854487187979360064357 73209910216347746130012067)
      ·
        refine ⟨109814865324521619195018101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73209910216347746130012067 109814865324521619195018101)
        ·
          refine ⟨10295143624173901799532947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109814865324521619195018101 10295143624173901799532947)
          ·
            refine ⟨15442715436260852699299421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10295143624173901799532947 15442715436260852699299421)
            ·
              refine ⟨5791018288597819762237283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15442715436260852699299421 5791018288597819762237283)
              ·
                refine ⟨8686527432896729643355925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5791018288597819762237283 8686527432896729643355925)
                ·
                  refine ⟨407180973417034202032309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8686527432896729643355925 407180973417034202032309)
                  ·
                    rfl

theorem cell23_7136839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 6].length) (baseStart_7136839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136839 prefixEnd_7136839 := by exact prefixLift 7136839
  have htrace : WordTrace (prefixWord ++ tailWord_7136839) baseStart_7136839 baseEnd_7136839 := by
    simpa [prefixWord, tailWord_7136839, baseEnd_7136839] using wordTrace_append hprefix tailTrace_7136839
  have hstable : (prefixWord ++ tailWord_7136839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136839).length < 2 ^ (prefixWord ++ tailWord_7136839).sum := by decide
  have hdescent : baseEnd_7136839 < baseStart_7136839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136842 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 3, 5, 2]
def baseStart_7136842 : Nat := 118140960795 + 7136842 * 2 ^ 59
def prefixEnd_7136842 : Nat := 4983230072969 + 3 ^ 40 * 7136842 * 2
def baseEnd_7136842 : Nat := 3664630301195271306553267

theorem tailTrace_7136842 : CollatzResearch.WordTrace tailWord_7136842 prefixEnd_7136842 3664630301195271306553267 := by
  unfold tailWord_7136842
  simp only [CollatzResearch.WordTrace]
  refine ⟨65075503102611946104767195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173534674940298522946045853 65075503102611946104767195)
  ·
    refine ⟨97613254653917919157150793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65075503102611946104767195 97613254653917919157150793)
    ·
      refine ⟨73209940990438439367863095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97613254653917919157150793 73209940990438439367863095)
      ·
        refine ⟨109814911485657659051794643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73209940990438439367863095 109814911485657659051794643)
        ·
          refine ⟨164722367228486488577691965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109814911485657659051794643 164722367228486488577691965)
          ·
            refine ⟨61770887710682433216634487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164722367228486488577691965 61770887710682433216634487)
            ·
              refine ⟨92656331566023649824951731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61770887710682433216634487 92656331566023649824951731)
              ·
                refine ⟨138984497349035474737427597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92656331566023649824951731 138984497349035474737427597)
                ·
                  refine ⟨52119186505888303026535349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138984497349035474737427597 52119186505888303026535349)
                  ·
                    refine ⟨4886173734927028408737689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52119186505888303026535349 4886173734927028408737689)
                    ·
                      refine ⟨3664630301195271306553267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4886173734927028408737689 3664630301195271306553267)
                      ·
                        rfl

theorem cell23_7136842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_7136842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136842 prefixEnd_7136842 := by exact prefixLift 7136842
  have htrace : WordTrace (prefixWord ++ tailWord_7136842) baseStart_7136842 baseEnd_7136842 := by
    simpa [prefixWord, tailWord_7136842, baseEnd_7136842] using wordTrace_append hprefix tailTrace_7136842
  have hstable : (prefixWord ++ tailWord_7136842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136842).length < 2 ^ (prefixWord ++ tailWord_7136842).sum := by decide
  have hdescent : baseEnd_7136842 < baseStart_7136842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136865 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 3, 6]
def baseStart_7136865 : Nat := 118140960795 + 7136865 * 2 ^ 59
def prefixEnd_7136865 : Nat := 4983230072969 + 3 ^ 40 * 7136865 * 2
def baseEnd_7136865 : Nat := 1221547370416774905521887

theorem tailTrace_7136865 : CollatzResearch.WordTrace tailWord_7136865 prefixEnd_7136865 1221547370416774905521887 := by
  unfold tailWord_7136865
  simp only [CollatzResearch.WordTrace]
  refine ⟨260302851289364459347156049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173535234192909639564770699 260302851289364459347156049)
  ·
    refine ⟨195227138467023344510367037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260302851289364459347156049 195227138467023344510367037)
    ·
      refine ⟨73210176925133754191387639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195227138467023344510367037 73210176925133754191387639)
      ·
        refine ⟨109815265387700631287081459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73210176925133754191387639 109815265387700631287081459)
        ·
          refine ⟨164722898081550946930622189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109815265387700631287081459 164722898081550946930622189)
          ·
            refine ⟨61771086780581605098983321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164722898081550946930622189 61771086780581605098983321)
            ·
              refine ⟨46328315085436203824237491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61771086780581605098983321 46328315085436203824237491)
              ·
                refine ⟨69492472628154305736356237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46328315085436203824237491 69492472628154305736356237)
                ·
                  refine ⟨26059677235557864651133589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69492472628154305736356237 26059677235557864651133589)
                  ·
                    refine ⟨1221547370416774905521887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26059677235557864651133589 1221547370416774905521887)
                    ·
                      rfl

theorem cell23_7136865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_7136865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136865 prefixEnd_7136865 := by exact prefixLift 7136865
  have htrace : WordTrace (prefixWord ++ tailWord_7136865) baseStart_7136865 baseEnd_7136865 := by
    simpa [prefixWord, tailWord_7136865, baseEnd_7136865] using wordTrace_append hprefix tailTrace_7136865
  have hstable : (prefixWord ++ tailWord_7136865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136865).length < 2 ^ (prefixWord ++ tailWord_7136865).sum := by decide
  have hdescent : baseEnd_7136865 < baseStart_7136865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136875 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 3]
def baseStart_7136875 : Nat := 118140960795 + 7136875 * 2 ^ 59
def prefixEnd_7136875 : Nat := 4983230072969 + 3 ^ 40 * 7136875 * 2
def baseEnd_7136875 : Nat := 3664647246056869677440615

theorem tailTrace_7136875 : CollatzResearch.WordTrace tailWord_7136875 prefixEnd_7136875 3664647246056869677440615 := by
  unfold tailWord_7136875
  simp only [CollatzResearch.WordTrace]
  refine ⟨260303216019328231055020079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173535477346218820703346719 260303216019328231055020079)
  ·
    refine ⟨390454824028992346582530119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260303216019328231055020079 390454824028992346582530119)
    ·
      refine ⟨585682236043488519873795179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390454824028992346582530119 585682236043488519873795179)
      ·
        refine ⟨878523354065232779810692769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585682236043488519873795179 878523354065232779810692769)
        ·
          refine ⟨658892515548924584858019577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 878523354065232779810692769 658892515548924584858019577)
          ·
            refine ⟨494169386661693438643514683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658892515548924584858019577 494169386661693438643514683)
            ·
              refine ⟨741254079992540157965272025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494169386661693438643514683 741254079992540157965272025)
              ·
                refine ⟨555940559994405118473954019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741254079992540157965272025 555940559994405118473954019)
                ·
                  refine ⟨833910839991607677710931029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555940559994405118473954019 833910839991607677710931029)
                  ·
                    refine ⟨9772392656151652473174973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 833910839991607677710931029 9772392656151652473174973)
                    ·
                      refine ⟨3664647246056869677440615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9772392656151652473174973 3664647246056869677440615)
                      ·
                        rfl

theorem cell23_7136875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 3].length) (baseStart_7136875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136875 prefixEnd_7136875 := by exact prefixLift 7136875
  have htrace : WordTrace (prefixWord ++ tailWord_7136875) baseStart_7136875 baseEnd_7136875 := by
    simpa [prefixWord, tailWord_7136875, baseEnd_7136875] using wordTrace_append hprefix tailTrace_7136875
  have hstable : (prefixWord ++ tailWord_7136875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136875).length < 2 ^ (prefixWord ++ tailWord_7136875).sum := by decide
  have hdescent : baseEnd_7136875 < baseStart_7136875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136892 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 3, 2, 3]
def baseStart_7136892 : Nat := 118140960795 + 7136892 * 2 ^ 59
def prefixEnd_7136892 : Nat := 4983230072969 + 3 ^ 40 * 7136892 * 2
def baseEnd_7136892 : Nat := 3664655975227996110928037

theorem tailTrace_7136892 : CollatzResearch.WordTrace tailWord_7136892 prefixEnd_7136892 3664655975227996110928037 := by
  unfold tailWord_7136892
  simp only [CollatzResearch.WordTrace]
  refine ⟨130151918030133321479194465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173535890706844428638925953 130151918030133321479194465)
  ·
    refine ⟨97613938522599991109395849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130151918030133321479194465 97613938522599991109395849)
    ·
      refine ⟨73210453891949993332046887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97613938522599991109395849 73210453891949993332046887)
      ·
        refine ⟨109815680837924989998070331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73210453891949993332046887 109815680837924989998070331)
        ·
          refine ⟨164723521256887484997105497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109815680837924989998070331 164723521256887484997105497)
          ·
            refine ⟨123542640942665613747829123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164723521256887484997105497 123542640942665613747829123)
            ·
              refine ⟨185313961413998420621743685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123542640942665613747829123 185313961413998420621743685)
              ·
                refine ⟨34746367765124703866576941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185313961413998420621743685 34746367765124703866576941)
                ·
                  refine ⟨13029887911921763949966353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34746367765124703866576941 13029887911921763949966353)
                  ·
                    refine ⟨9772415933941322962474765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13029887911921763949966353 9772415933941322962474765)
                    ·
                      refine ⟨3664655975227996110928037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9772415933941322962474765 3664655975227996110928037)
                      ·
                        rfl

theorem cell23_7136892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_7136892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136892 prefixEnd_7136892 := by exact prefixLift 7136892
  have htrace : WordTrace (prefixWord ++ tailWord_7136892) baseStart_7136892 baseEnd_7136892 := by
    simpa [prefixWord, tailWord_7136892, baseEnd_7136892] using wordTrace_append hprefix tailTrace_7136892
  have hstable : (prefixWord ++ tailWord_7136892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136892).length < 2 ^ (prefixWord ++ tailWord_7136892).sum := by decide
  have hdescent : baseEnd_7136892 < baseStart_7136892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136906 : List Nat := [3, 1, 2, 3, 2, 3, 1, 2, 1, 1, 4]
def baseStart_7136906 : Nat := 118140960795 + 7136906 * 2 ^ 59
def prefixEnd_7136906 : Nat := 4983230072969 + 3 ^ 40 * 7136906 * 2
def baseEnd_7136906 : Nat := 3664663163957159056152973

theorem tailTrace_7136906 : CollatzResearch.WordTrace tailWord_7136906 prefixEnd_7136906 3664663163957159056152973 := by
  unfold tailWord_7136906
  simp only [CollatzResearch.WordTrace]
  refine ⟨65076086670553980837349643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173536231121477282232932381 65076086670553980837349643)
  ·
    refine ⟨97614130005830971256024465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65076086670553980837349643 97614130005830971256024465)
    ·
      refine ⟨73210597504373228442018349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97614130005830971256024465 73210597504373228442018349)
      ·
        refine ⟨27453974064139960665756881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73210597504373228442018349 27453974064139960665756881)
        ·
          refine ⟨20590480548104970499317661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27453974064139960665756881 20590480548104970499317661)
          ·
            refine ⟨7721430205539363937244123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20590480548104970499317661 7721430205539363937244123)
            ·
              refine ⟨11582145308309045905866185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7721430205539363937244123 11582145308309045905866185)
              ·
                refine ⟨8686608981231784429399639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11582145308309045905866185 8686608981231784429399639)
                ·
                  refine ⟨13029913471847676644099459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8686608981231784429399639 13029913471847676644099459)
                  ·
                    refine ⟨19544870207771514966149189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13029913471847676644099459 19544870207771514966149189)
                    ·
                      refine ⟨3664663163957159056152973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19544870207771514966149189 3664663163957159056152973)
                      ·
                        rfl

theorem cell23_7136906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_7136906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136906 prefixEnd_7136906 := by exact prefixLift 7136906
  have htrace : WordTrace (prefixWord ++ tailWord_7136906) baseStart_7136906 baseEnd_7136906 := by
    simpa [prefixWord, tailWord_7136906, baseEnd_7136906] using wordTrace_append hprefix tailTrace_7136906
  have hstable : (prefixWord ++ tailWord_7136906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136906).length < 2 ^ (prefixWord ++ tailWord_7136906).sum := by decide
  have hdescent : baseEnd_7136906 < baseStart_7136906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136926 : List Nat := [4, 3, 1, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_7136926 : Nat := 118140960795 + 7136926 * 2 ^ 59
def prefixEnd_7136926 : Nat := 4983230072969 + 3 ^ 40 * 7136926 * 2
def baseEnd_7136926 : Nat := 3664673433570248977902881

theorem tailTrace_7136926 : CollatzResearch.WordTrace tailWord_7136926 prefixEnd_7136926 3664673433570248977902881 := by
  unfold tailWord_7136926
  simp only [CollatzResearch.WordTrace]
  refine ⟨32538134517767933345640829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173536717428095644510084421 32538134517767933345640829)
  ·
    refine ⟨12201800444162975004615311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32538134517767933345640829 12201800444162975004615311)
    ·
      refine ⟨18302700666244462506922967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12201800444162975004615311 18302700666244462506922967)
      ·
        refine ⟨27454050999366693760384451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18302700666244462506922967 27454050999366693760384451)
        ·
          refine ⟨41181076499050040640576677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27454050999366693760384451 41181076499050040640576677)
          ·
            refine ⟨7721451843571882620108127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41181076499050040640576677 7721451843571882620108127)
            ·
              refine ⟨11582177765357823930162191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7721451843571882620108127 11582177765357823930162191)
              ·
                refine ⟨17373266648036735895243287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11582177765357823930162191 17373266648036735895243287)
                ·
                  refine ⟨26059899972055103842864931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17373266648036735895243287 26059899972055103842864931)
                  ·
                    refine ⟨39089849958082655764297397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26059899972055103842864931 39089849958082655764297397)
                    ·
                      refine ⟨3664673433570248977902881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39089849958082655764297397 3664673433570248977902881)
                      ·
                        rfl

theorem cell23_7136926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_7136926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136926 prefixEnd_7136926 := by exact prefixLift 7136926
  have htrace : WordTrace (prefixWord ++ tailWord_7136926) baseStart_7136926 baseEnd_7136926 := by
    simpa [prefixWord, tailWord_7136926, baseEnd_7136926] using wordTrace_append hprefix tailTrace_7136926
  have hstable : (prefixWord ++ tailWord_7136926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136926).length < 2 ^ (prefixWord ++ tailWord_7136926).sum := by decide
  have hdescent : baseEnd_7136926 < baseStart_7136926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136956 : List Nat := [2, 2, 2, 3, 1, 2, 2, 3, 2, 1, 3]
def baseStart_7136956 : Nat := 118140960795 + 7136956 * 2 ^ 59
def prefixEnd_7136956 : Nat := 4983230072969 + 3 ^ 40 * 7136956 * 2
def baseEnd_7136956 : Nat := 3664688837989883860527743

theorem tailTrace_7136956 : CollatzResearch.WordTrace tailWord_7136956 prefixEnd_7136956 3664688837989883860527743 := by
  unfold tailWord_7136956
  simp only [CollatzResearch.WordTrace]
  refine ⟨130153085166017390944359361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173537446888023187925812481 130153085166017390944359361)
  ·
    refine ⟨97614813874513043208269521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130153085166017390944359361 97614813874513043208269521)
    ·
      refine ⟨73211110405884782406202141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97614813874513043208269521 73211110405884782406202141)
      ·
        refine ⟨27454166402206793402325803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73211110405884782406202141 27454166402206793402325803)
        ·
          refine ⟨41181249603310190103488705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27454166402206793402325803 41181249603310190103488705)
          ·
            refine ⟨30885937202482642577616529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41181249603310190103488705 30885937202482642577616529)
            ·
              refine ⟨23164452901861981933212397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30885937202482642577616529 23164452901861981933212397)
              ·
                refine ⟨8686669838198243224954649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23164452901861981933212397 8686669838198243224954649)
                ·
                  refine ⟨6515002378648682418715987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8686669838198243224954649 6515002378648682418715987)
                  ·
                    refine ⟨9772503567973023628073981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6515002378648682418715987 9772503567973023628073981)
                    ·
                      refine ⟨3664688837989883860527743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9772503567973023628073981 3664688837989883860527743)
                      ·
                        rfl

theorem cell23_7136956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_7136956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136956 prefixEnd_7136956 := by exact prefixLift 7136956
  have htrace : WordTrace (prefixWord ++ tailWord_7136956) baseStart_7136956 baseEnd_7136956 := by
    simpa [prefixWord, tailWord_7136956, baseEnd_7136956] using wordTrace_append hprefix tailTrace_7136956
  have hstable : (prefixWord ++ tailWord_7136956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136956).length < 2 ^ (prefixWord ++ tailWord_7136956).sum := by decide
  have hdescent : baseEnd_7136956 < baseStart_7136956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136992 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 4]
def baseStart_7136992 : Nat := 118140960795 + 7136992 * 2 ^ 59
def prefixEnd_7136992 : Nat := 4983230072969 + 3 ^ 40 * 7136992 * 2
def baseEnd_7136992 : Nat := 3664707323293445719677577

theorem tailTrace_7136992 : CollatzResearch.WordTrace tailWord_7136992 prefixEnd_7136992 3664707323293445719677577 := by
  unfold tailWord_7136992
  simp only [CollatzResearch.WordTrace]
  refine ⟨130153741679952180018514615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173538322239936240024686153 130153741679952180018514615)
  ·
    refine ⟨195230612519928270027771923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130153741679952180018514615 195230612519928270027771923)
    ·
      refine ⟨292845918779892405041657885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195230612519928270027771923 292845918779892405041657885)
      ·
        refine ⟨109817219542459651890621707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292845918779892405041657885 109817219542459651890621707)
        ·
          refine ⟨164725829313689477835932561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109817219542459651890621707 164725829313689477835932561)
          ·
            refine ⟨123544371985267108376949421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164725829313689477835932561 123544371985267108376949421)
            ·
              refine ⟨46329139494475165641356033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123544371985267108376949421 46329139494475165641356033)
              ·
                refine ⟨34746854620856374231017025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46329139494475165641356033 34746854620856374231017025)
                ·
                  refine ⟨26060140965642280673262769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34746854620856374231017025 26060140965642280673262769)
                  ·
                    refine ⟨19545105724231710504947077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26060140965642280673262769 19545105724231710504947077)
                    ·
                      refine ⟨3664707323293445719677577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19545105724231710504947077 3664707323293445719677577)
                      ·
                        rfl

theorem cell23_7136992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_7136992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136992 prefixEnd_7136992 := by exact prefixLift 7136992
  have htrace : WordTrace (prefixWord ++ tailWord_7136992) baseStart_7136992 baseEnd_7136992 := by
    simpa [prefixWord, tailWord_7136992, baseEnd_7136992] using wordTrace_append hprefix tailTrace_7136992
  have hstable : (prefixWord ++ tailWord_7136992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136992).length < 2 ^ (prefixWord ++ tailWord_7136992).sum := by decide
  have hdescent : baseEnd_7136992 < baseStart_7136992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7136996 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 4, 2, 2]
def baseStart_7136996 : Nat := 118140960795 + 7136996 * 2 ^ 59
def prefixEnd_7136996 : Nat := 4983230072969 + 3 ^ 40 * 7136996 * 2
def baseEnd_7136996 : Nat := 3664709377216063704027559

theorem tailTrace_7136996 : CollatzResearch.WordTrace tailWord_7136996 prefixEnd_7136996 3664709377216063704027559 := by
  unfold tailWord_7136996
  simp only [CollatzResearch.WordTrace]
  refine ⟨130153814625944934360087421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173538419501259912480116561 130153814625944934360087421)
  ·
    refine ⟨48807680484729350385032783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130153814625944934360087421 48807680484729350385032783)
    ·
      refine ⟨73211520727094025577549175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48807680484729350385032783 73211520727094025577549175)
      ·
        refine ⟨109817281090641038366323763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73211520727094025577549175 109817281090641038366323763)
        ·
          refine ⟨164725921635961557549485645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109817281090641038366323763 164725921635961557549485645)
          ·
            refine ⟨61772220613485584081057117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164725921635961557549485645 61772220613485584081057117)
            ·
              refine ⟨23164582730057094030396419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61772220613485584081057117 23164582730057094030396419)
              ·
                refine ⟨34746874095085641045594629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23164582730057094030396419 34746874095085641045594629)
                ·
                  refine ⟨6515038892828557696048993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34746874095085641045594629 6515038892828557696048993)
                  ·
                    refine ⟨4886279169621418272036745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6515038892828557696048993 4886279169621418272036745)
                    ·
                      refine ⟨3664709377216063704027559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4886279169621418272036745 3664709377216063704027559)
                      ·
                        rfl

theorem cell23_7136996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_7136996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7136996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7136996 prefixEnd_7136996 := by exact prefixLift 7136996
  have htrace : WordTrace (prefixWord ++ tailWord_7136996) baseStart_7136996 baseEnd_7136996 := by
    simpa [prefixWord, tailWord_7136996, baseEnd_7136996] using wordTrace_append hprefix tailTrace_7136996
  have hstable : (prefixWord ++ tailWord_7136996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7136996).length < 2 ^ (prefixWord ++ tailWord_7136996).sum := by decide
  have hdescent : baseEnd_7136996 < baseStart_7136996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7136996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137002 : List Nat := [3, 1, 3, 1, 1, 1, 3, 3, 7]
def baseStart_7137002 : Nat := 118140960795 + 7137002 * 2 ^ 59
def prefixEnd_7137002 : Nat := 4983230072969 + 3 ^ 40 * 7137002 * 2
def baseEnd_7137002 : Nat := 407190273122221186728059

theorem tailTrace_7137002 : CollatzResearch.WordTrace tailWord_7137002 prefixEnd_7137002 407190273122221186728059 := by
  unfold tailWord_7137002
  simp only [CollatzResearch.WordTrace]
  refine ⟨65076962022467032936223315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173538565393245421163262173 65076962022467032936223315)
  ·
    refine ⟨97615443033700549404334973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65076962022467032936223315 97615443033700549404334973)
    ·
      refine ⟨36605791137637706026625615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97615443033700549404334973 36605791137637706026625615)
      ·
        refine ⟨54908686706456559039938423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36605791137637706026625615 54908686706456559039938423)
        ·
          refine ⟨82363030059684838559907635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54908686706456559039938423 82363030059684838559907635)
          ·
            refine ⟨123544545089527257839861453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82363030059684838559907635 123544545089527257839861453)
            ·
              refine ⟨46329204408572721689948045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123544545089527257839861453 46329204408572721689948045)
              ·
                refine ⟨17373451653214770633730517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46329204408572721689948045 17373451653214770633730517)
                ·
                  refine ⟨407190273122221186728059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17373451653214770633730517 407190273122221186728059)
                  ·
                    rfl

theorem cell23_7137002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 7].length) (baseStart_7137002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137002 prefixEnd_7137002 := by exact prefixLift 7137002
  have htrace : WordTrace (prefixWord ++ tailWord_7137002) baseStart_7137002 baseEnd_7137002 := by
    simpa [prefixWord, tailWord_7137002, baseEnd_7137002] using wordTrace_append hprefix tailTrace_7137002
  have hstable : (prefixWord ++ tailWord_7137002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137002).length < 2 ^ (prefixWord ++ tailWord_7137002).sum := by decide
  have hdescent : baseEnd_7137002 < baseStart_7137002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137032 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 1, 7]
def baseStart_7137032 : Nat := 118140960795 + 7137032 * 2 ^ 59
def prefixEnd_7137032 : Nat := 4983230072969 + 3 ^ 40 * 7137032 * 2
def baseEnd_7137032 : Nat := 1221575954173208521059131

theorem tailTrace_7137032 : CollatzResearch.WordTrace tailWord_7137032 prefixEnd_7137032 1221575954173208521059131 := by
  unfold tailWord_7137032
  simp only [CollatzResearch.WordTrace]
  refine ⟨130154471139879723434242675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173539294853172964578990233 130154471139879723434242675)
  ·
    refine ⟨195231706709819585151364013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130154471139879723434242675 195231706709819585151364013)
    ·
      refine ⟨73211890016182344431761505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195231706709819585151364013 73211890016182344431761505)
      ·
        refine ⟨54908917512136758323821129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73211890016182344431761505 54908917512136758323821129)
        ·
          refine ⟨41181688134102568742865847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54908917512136758323821129 41181688134102568742865847)
          ·
            refine ⟨61772532201153853114298771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41181688134102568742865847 61772532201153853114298771)
            ·
              refine ⟨92658798301730779671448157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61772532201153853114298771 92658798301730779671448157)
              ·
                refine ⟨34747049363149042376793059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92658798301730779671448157 34747049363149042376793059)
                ·
                  refine ⟨52120574044723563565189589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34747049363149042376793059 52120574044723563565189589)
                  ·
                    refine ⟨1221575954173208521059131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52120574044723563565189589 1221575954173208521059131)
                    ·
                      rfl

theorem cell23_7137032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_7137032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137032 prefixEnd_7137032 := by exact prefixLift 7137032
  have htrace : WordTrace (prefixWord ++ tailWord_7137032) baseStart_7137032 baseEnd_7137032 := by
    simpa [prefixWord, tailWord_7137032, baseEnd_7137032] using wordTrace_append hprefix tailTrace_7137032
  have hstable : (prefixWord ++ tailWord_7137032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137032).length < 2 ^ (prefixWord ++ tailWord_7137032).sum := by decide
  have hdescent : baseEnd_7137032 < baseStart_7137032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137086 : List Nat := [4, 2, 1, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_7137086 : Nat := 118140960795 + 7137086 * 2 ^ 59
def prefixEnd_7137086 : Nat := 4983230072969 + 3 ^ 40 * 7137086 * 2
def baseEnd_7137086 : Nat := 3664755590474968351902145

theorem tailTrace_7137086 : CollatzResearch.WordTrace tailWord_7137086 prefixEnd_7137086 3664755590474968351902145 := by
  unfold tailWord_7137086
  simp only [CollatzResearch.WordTrace]
  refine ⟨32538863977695476761368889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173540607881042542727300741 32538863977695476761368889)
  ·
    refine ⟨24404147983271607571026667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32538863977695476761368889 24404147983271607571026667)
    ·
      refine ⟨36606221974907411356540001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24404147983271607571026667 36606221974907411356540001)
      ·
        refine ⟨27454666481180558517405001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36606221974907411356540001 27454666481180558517405001)
        ·
          refine ⟨20590999860885418888053751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27454666481180558517405001 20590999860885418888053751)
          ·
            refine ⟨30886499791328128332080627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20590999860885418888053751 30886499791328128332080627)
            ·
              refine ⟨46329749686992192498120941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30886499791328128332080627 46329749686992192498120941)
              ·
                refine ⟨17373656132622072186795353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46329749686992192498120941 17373656132622072186795353)
                ·
                  refine ⟨13030242099466554140096515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17373656132622072186795353 13030242099466554140096515)
                  ·
                    refine ⟨19545363149199831210144773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13030242099466554140096515 19545363149199831210144773)
                    ·
                      refine ⟨3664755590474968351902145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19545363149199831210144773 3664755590474968351902145)
                      ·
                        rfl

theorem cell23_7137086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_7137086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137086 prefixEnd_7137086 := by exact prefixLift 7137086
  have htrace : WordTrace (prefixWord ++ tailWord_7137086) baseStart_7137086 baseEnd_7137086 := by
    simpa [prefixWord, tailWord_7137086, baseEnd_7137086] using wordTrace_append hprefix tailTrace_7137086
  have hstable : (prefixWord ++ tailWord_7137086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137086).length < 2 ^ (prefixWord ++ tailWord_7137086).sum := by decide
  have hdescent : baseEnd_7137086 < baseStart_7137086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137106 : List Nat := [3, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_7137106 : Nat := 118140960795 + 7137106 * 2 ^ 59
def prefixEnd_7137106 : Nat := 4983230072969 + 3 ^ 40 * 7137106 * 2
def baseEnd_7137106 : Nat := 3664765860088058273652053

theorem tailTrace_7137106 : CollatzResearch.WordTrace tailWord_7137106 prefixEnd_7137106 3664765860088058273652053 := by
  unfold tailWord_7137106
  simp only [CollatzResearch.WordTrace]
  refine ⟨65077910320372839376669793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173541094187660905004452781 65077910320372839376669793)
  ·
    refine ⟨48808432740279629532502345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65077910320372839376669793 48808432740279629532502345)
    ·
      refine ⟨36606324555209722149376759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48808432740279629532502345 36606324555209722149376759)
      ·
        refine ⟨54909486832814583224065139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36606324555209722149376759 54909486832814583224065139)
        ·
          refine ⟨82364230249221874836097709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54909486832814583224065139 82364230249221874836097709)
          ·
            refine ⟨30886586343458203063536641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82364230249221874836097709 30886586343458203063536641)
            ·
              refine ⟨23164939757593652297652481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30886586343458203063536641 23164939757593652297652481)
              ·
                refine ⟨17373704818195239223239361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23164939757593652297652481 17373704818195239223239361)
                ·
                  refine ⟨13030278613646429417429521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17373704818195239223239361 13030278613646429417429521)
                  ·
                    refine ⟨9772708960234822063072141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13030278613646429417429521 9772708960234822063072141)
                    ·
                      refine ⟨3664765860088058273652053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9772708960234822063072141 3664765860088058273652053)
                      ·
                        rfl

theorem cell23_7137106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_7137106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137106 prefixEnd_7137106 := by exact prefixLift 7137106
  have htrace : WordTrace (prefixWord ++ tailWord_7137106) baseStart_7137106 baseEnd_7137106 := by
    simpa [prefixWord, tailWord_7137106, baseEnd_7137106] using wordTrace_append hprefix tailTrace_7137106
  have hstable : (prefixWord ++ tailWord_7137106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137106).length < 2 ^ (prefixWord ++ tailWord_7137106).sum := by decide
  have hdescent : baseEnd_7137106 < baseStart_7137106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137109 : List Nat := [1, 3, 2, 2, 2, 2, 1, 4, 6]
def baseStart_7137109 : Nat := 118140960795 + 7137109 * 2 ^ 59
def prefixEnd_7137109 : Nat := 4983230072969 + 3 ^ 40 * 7137109 * 2
def baseEnd_7137109 : Nat := 407196377836669084657171

theorem tailTrace_7137109 : CollatzResearch.WordTrace tailWord_7137109 prefixEnd_7137109 407196377836669084657171 := by
  unfold tailWord_7137109
  simp only [CollatzResearch.WordTrace]
  refine ⟨260311750700480489019038381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173541167133653659346025587 260311750700480489019038381)
  ·
    refine ⟨97616906512680183382139393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260311750700480489019038381 97616906512680183382139393)
    ·
      refine ⟨73212679884510137536604545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97616906512680183382139393 73212679884510137536604545)
      ·
        refine ⟨54909509913382603152453409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73212679884510137536604545 54909509913382603152453409)
        ·
          refine ⟨41182132435036952364340057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54909509913382603152453409 41182132435036952364340057)
          ·
            refine ⟨30886599326277714273255043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41182132435036952364340057 30886599326277714273255043)
            ·
              refine ⟨46329898989416571409882565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30886599326277714273255043 46329898989416571409882565)
              ·
                refine ⟨8686856060515607139352981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46329898989416571409882565 8686856060515607139352981)
                ·
                  refine ⟨407196377836669084657171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8686856060515607139352981 407196377836669084657171)
                  ·
                    rfl

theorem cell23_7137109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 6].length) (baseStart_7137109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137109 prefixEnd_7137109 := by exact prefixLift 7137109
  have htrace : WordTrace (prefixWord ++ tailWord_7137109) baseStart_7137109 baseEnd_7137109 := by
    simpa [prefixWord, tailWord_7137109, baseEnd_7137109] using wordTrace_append hprefix tailTrace_7137109
  have hstable : (prefixWord ++ tailWord_7137109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137109).length < 2 ^ (prefixWord ++ tailWord_7137109).sum := by decide
  have hdescent : baseEnd_7137109 < baseStart_7137109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137139 : List Nat := [1, 1, 1, 2, 2, 1, 3, 6, 1, 5]
def baseStart_7137139 : Nat := 118140960795 + 7137139 * 2 ^ 59
def prefixEnd_7137139 : Nat := 4983230072969 + 3 ^ 40 * 7137139 * 2
def baseEnd_7137139 : Nat := 1221594268316552214846467

theorem tailTrace_7137139 : CollatzResearch.WordTrace tailWord_7137139 prefixEnd_7137139 1221594268316552214846467 := by
  unfold tailWord_7137139
  simp only [CollatzResearch.WordTrace]
  refine ⟨260312844890371804142630471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173541896593581202761753647 260312844890371804142630471)
  ·
    refine ⟨390469267335557706213945707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260312844890371804142630471 390469267335557706213945707)
    ·
      refine ⟨585703901003336559320918561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390469267335557706213945707 585703901003336559320918561)
      ·
        refine ⟨439277925752502419490688921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585703901003336559320918561 439277925752502419490688921)
        ·
          refine ⟨329458444314376814618016691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439277925752502419490688921 329458444314376814618016691)
          ·
            refine ⟨494187666471565221927025037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329458444314376814618016691 494187666471565221927025037)
            ·
              refine ⟨185320374926836958222634389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 494187666471565221927025037 185320374926836958222634389)
              ·
                refine ⟨8686892574695482416685987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 185320374926836958222634389 8686892574695482416685987)
                ·
                  refine ⟨13030338862043223625028981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8686892574695482416685987 13030338862043223625028981)
                  ·
                    refine ⟨1221594268316552214846467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13030338862043223625028981 1221594268316552214846467)
                    ·
                      rfl

theorem cell23_7137139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 5].length) (baseStart_7137139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137139 prefixEnd_7137139 := by exact prefixLift 7137139
  have htrace : WordTrace (prefixWord ++ tailWord_7137139) baseStart_7137139 baseEnd_7137139 := by
    simpa [prefixWord, tailWord_7137139, baseEnd_7137139] using wordTrace_append hprefix tailTrace_7137139
  have hstable : (prefixWord ++ tailWord_7137139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137139).length < 2 ^ (prefixWord ++ tailWord_7137139).sum := by decide
  have hdescent : baseEnd_7137139 < baseStart_7137139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137170 : List Nat := [3, 2, 3, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_7137170 : Nat := 118140960795 + 7137170 * 2 ^ 59
def prefixEnd_7137170 : Nat := 4983230072969 + 3 ^ 40 * 7137170 * 2
def baseEnd_7137170 : Nat := 3664798722849946023251759

theorem tailTrace_7137170 : CollatzResearch.WordTrace tailWord_7137170 prefixEnd_7137170 3664798722849946023251759 := by
  unfold tailWord_7137170
  simp only [CollatzResearch.WordTrace]
  refine ⟨65078493888314874109252241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173542650368839664291339309 65078493888314874109252241)
  ·
    refine ⟨48808870416236155581939181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65078493888314874109252241 48808870416236155581939181)
    ·
      refine ⟨18303326406088558343227193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48808870416236155581939181 18303326406088558343227193)
      ·
        refine ⟨13727494804566418757420395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18303326406088558343227193 13727494804566418757420395)
        ·
          refine ⟨20591242206849628136130593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13727494804566418757420395 20591242206849628136130593)
          ·
            refine ⟨15443431655137221102097945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20591242206849628136130593 15443431655137221102097945)
            ·
              refine ⟨11582573741352915826573459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15443431655137221102097945 11582573741352915826573459)
              ·
                refine ⟨17373860612029373739860189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11582573741352915826573459 17373860612029373739860189)
                ·
                  refine ⟨6515197729511015152447571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17373860612029373739860189 6515197729511015152447571)
                  ·
                    refine ⟨9772796594266522728671357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6515197729511015152447571 9772796594266522728671357)
                    ·
                      refine ⟨3664798722849946023251759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9772796594266522728671357 3664798722849946023251759)
                      ·
                        rfl

theorem cell23_7137170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_7137170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137170 prefixEnd_7137170 := by exact prefixLift 7137170
  have htrace : WordTrace (prefixWord ++ tailWord_7137170) baseStart_7137170 baseEnd_7137170 := by
    simpa [prefixWord, tailWord_7137170, baseEnd_7137170] using wordTrace_append hprefix tailTrace_7137170
  have hstable : (prefixWord ++ tailWord_7137170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137170).length < 2 ^ (prefixWord ++ tailWord_7137170).sum := by decide
  have hdescent : baseEnd_7137170 < baseStart_7137170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137210 : List Nat := [3, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2]
def baseStart_7137210 : Nat := 118140960795 + 7137210 * 2 ^ 59
def prefixEnd_7137210 : Nat := 4983230072969 + 3 ^ 40 * 7137210 * 2
def baseEnd_7137210 : Nat := 3664819262076125866751575

theorem tailTrace_7137210 : CollatzResearch.WordTrace tailWord_7137210 prefixEnd_7137210 3664819262076125866751575 := by
  unfold tailWord_7137210
  simp only [CollatzResearch.WordTrace]
  refine ⟨65078858618278645817116271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173543622982076388845643389 65078858618278645817116271)
  ·
    refine ⟨97618287927417968725674407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65078858618278645817116271 97618287927417968725674407)
    ·
      refine ⟨146427431891126953088511611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97618287927417968725674407 146427431891126953088511611)
      ·
        refine ⟨219641147836690429632767417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146427431891126953088511611 219641147836690429632767417)
        ·
          refine ⟨164730860877517822224575563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219641147836690429632767417 164730860877517822224575563)
          ·
            refine ⟨247096291316276733336863345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164730860877517822224575563 247096291316276733336863345)
            ·
              refine ⟨185322218487207550002647509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247096291316276733336863345 185322218487207550002647509)
              ·
                refine ⟨4343489495793926953187051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 185322218487207550002647509 4343489495793926953187051)
                ·
                  refine ⟨6515234243690890429780577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4343489495793926953187051 6515234243690890429780577)
                  ·
                    refine ⟨4886425682768167822335433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6515234243690890429780577 4886425682768167822335433)
                    ·
                      refine ⟨3664819262076125866751575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4886425682768167822335433 3664819262076125866751575)
                      ·
                        rfl

theorem cell23_7137210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2].length) (baseStart_7137210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137210 prefixEnd_7137210 := by exact prefixLift 7137210
  have htrace : WordTrace (prefixWord ++ tailWord_7137210) baseStart_7137210 baseEnd_7137210 := by
    simpa [prefixWord, tailWord_7137210, baseEnd_7137210] using wordTrace_append hprefix tailTrace_7137210
  have hstable : (prefixWord ++ tailWord_7137210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137210).length < 2 ^ (prefixWord ++ tailWord_7137210).sum := by decide
  have hdescent : baseEnd_7137210 < baseStart_7137210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137213 : List Nat := [1, 4, 1, 2, 3, 1, 2, 3, 1, 2, 3]
def baseStart_7137213 : Nat := 118140960795 + 7137213 * 2 ^ 59
def prefixEnd_7137213 : Nat := 4983230072969 + 3 ^ 40 * 7137213 * 2
def baseEnd_7137213 : Nat := 3664820802518089355014061

theorem tailTrace_7137213 : CollatzResearch.WordTrace tailWord_7137213 prefixEnd_7137213 3664820802518089355014061 := by
  unfold tailWord_7137213
  simp only [CollatzResearch.WordTrace]
  refine ⟨260315543892103714780824293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173543695928069143187216195 260315543892103714780824293)
  ·
    refine ⟨48809164479769446521404555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260315543892103714780824293 48809164479769446521404555)
    ·
      refine ⟨73213746719654169782106833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48809164479769446521404555 73213746719654169782106833)
      ·
        refine ⟨54910310039740627336580125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73213746719654169782106833 54910310039740627336580125)
        ·
          refine ⟨20591366264902735251217547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54910310039740627336580125 20591366264902735251217547)
          ·
            refine ⟨30887049397354102876826321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20591366264902735251217547 30887049397354102876826321)
            ·
              refine ⟨23165287048015577157619741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30887049397354102876826321 23165287048015577157619741)
              ·
                refine ⟨8686982643005841434107403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23165287048015577157619741 8686982643005841434107403)
                ·
                  refine ⟨13030473964508762151161105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8686982643005841434107403 13030473964508762151161105)
                  ·
                    refine ⟨9772855473381571613370829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13030473964508762151161105 9772855473381571613370829)
                    ·
                      refine ⟨3664820802518089355014061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9772855473381571613370829 3664820802518089355014061)
                      ·
                        rfl

theorem cell23_7137213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_7137213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137213 prefixEnd_7137213 := by exact prefixLift 7137213
  have htrace : WordTrace (prefixWord ++ tailWord_7137213) baseStart_7137213 baseEnd_7137213 := by
    simpa [prefixWord, tailWord_7137213, baseEnd_7137213] using wordTrace_append hprefix tailTrace_7137213
  have hstable : (prefixWord ++ tailWord_7137213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137213).length < 2 ^ (prefixWord ++ tailWord_7137213).sum := by decide
  have hdescent : baseEnd_7137213 < baseStart_7137213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137227 : List Nat := [1, 1, 1, 1, 3, 4, 5, 2, 1, 2, 2]
def baseStart_7137227 : Nat := 118140960795 + 7137227 * 2 ^ 59
def prefixEnd_7137227 : Nat := 4983230072969 + 3 ^ 40 * 7137227 * 2
def baseEnd_7137227 : Nat := 3664827991247252300238997

theorem tailTrace_7137227 : CollatzResearch.WordTrace tailWord_7137227 prefixEnd_7137227 3664827991247252300238997 := by
  unfold tailWord_7137227
  simp only [CollatzResearch.WordTrace]
  refine ⟨260316054514052995171833935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173544036342701996781222623 260316054514052995171833935)
  ·
    refine ⟨390474081771079492757750903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260316054514052995171833935 390474081771079492757750903)
    ·
      refine ⟨585711122656619239136626355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390474081771079492757750903 585711122656619239136626355)
      ·
        refine ⟨878566683984928858704939533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585711122656619239136626355 878566683984928858704939533)
        ·
          refine ⟨329462506494348322014352325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 878566683984928858704939533 329462506494348322014352325)
          ·
            refine ⟨61774219967690310377691061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 329462506494348322014352325 61774219967690310377691061)
            ·
              refine ⟨5791333121970966597908537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61774219967690310377691061 5791333121970966597908537)
              ·
                refine ⟨4343499841478224948431403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5791333121970966597908537 4343499841478224948431403)
                ·
                  refine ⟨6515249762217337422647105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4343499841478224948431403 6515249762217337422647105)
                  ·
                    refine ⟨4886437321663003066985329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6515249762217337422647105 4886437321663003066985329)
                    ·
                      refine ⟨3664827991247252300238997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4886437321663003066985329 3664827991247252300238997)
                      ·
                        rfl

theorem cell23_7137227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 1, 2, 2].length) (baseStart_7137227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137227 prefixEnd_7137227 := by exact prefixLift 7137227
  have htrace : WordTrace (prefixWord ++ tailWord_7137227) baseStart_7137227 baseEnd_7137227 := by
    simpa [prefixWord, tailWord_7137227, baseEnd_7137227] using wordTrace_append hprefix tailTrace_7137227
  have hstable : (prefixWord ++ tailWord_7137227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137227).length < 2 ^ (prefixWord ++ tailWord_7137227).sum := by decide
  have hdescent : baseEnd_7137227 < baseStart_7137227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137244 : List Nat := [2, 2, 6, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_7137244 : Nat := 118140960795 + 7137244 * 2 ^ 59
def prefixEnd_7137244 : Nat := 4983230072969 + 3 ^ 40 * 7137244 * 2
def baseEnd_7137244 : Nat := 3664836720418378733726419

theorem tailTrace_7137244 : CollatzResearch.WordTrace tailWord_7137244 prefixEnd_7137244 3664836720418378733726419 := by
  unfold tailWord_7137244
  simp only [CollatzResearch.WordTrace]
  refine ⟨130158337277495703537601393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173544449703327604716801857 130158337277495703537601393)
  ·
    refine ⟨97618752958121777653201045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130158337277495703537601393 97618752958121777653201045)
    ·
      refine ⟨4575879044911958327493799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97618752958121777653201045 4575879044911958327493799)
      ·
        refine ⟨6863818567367937491240699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4575879044911958327493799 6863818567367937491240699)
        ·
          refine ⟨10295727851051906236861049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6863818567367937491240699 10295727851051906236861049)
          ·
            refine ⟨7721795888288929677645787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10295727851051906236861049 7721795888288929677645787)
            ·
              refine ⟨11582693832433394516468681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7721795888288929677645787 11582693832433394516468681)
              ·
                refine ⟨8687020374325045887351511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11582693832433394516468681 8687020374325045887351511)
                ·
                  refine ⟨13030530561487568831027267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8687020374325045887351511 13030530561487568831027267)
                  ·
                    refine ⟨19545795842231353246540901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13030530561487568831027267 19545795842231353246540901)
                    ·
                      refine ⟨3664836720418378733726419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19545795842231353246540901 3664836720418378733726419)
                      ·
                        rfl

theorem cell23_7137244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_7137244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137244 prefixEnd_7137244 := by exact prefixLift 7137244
  have htrace : WordTrace (prefixWord ++ tailWord_7137244) baseStart_7137244 baseEnd_7137244 := by
    simpa [prefixWord, tailWord_7137244, baseEnd_7137244] using wordTrace_append hprefix tailTrace_7137244
  have hstable : (prefixWord ++ tailWord_7137244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137244).length < 2 ^ (prefixWord ++ tailWord_7137244).sum := by decide
  have hdescent : baseEnd_7137244 < baseStart_7137244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137279 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 4]
def baseStart_7137279 : Nat := 118140960795 + 7137279 * 2 ^ 59
def prefixEnd_7137279 : Nat := 4983230072969 + 3 ^ 40 * 7137279 * 2
def baseEnd_7137279 : Nat := 3664854692241286096788757

theorem tailTrace_7137279 : CollatzResearch.WordTrace tailWord_7137279 prefixEnd_7137279 3664854692241286096788757 := by
  unfold tailWord_7137279
  simp only [CollatzResearch.WordTrace]
  refine ⟨260317951109864608052726891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173545300739909738701817927 260317951109864608052726891)
  ·
    refine ⟨390476926664796912079090337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260317951109864608052726891 390476926664796912079090337)
    ·
      refine ⟨292857694998597684059317753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390476926664796912079090337 292857694998597684059317753)
      ·
        refine ⟨219643271248948263044488315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292857694998597684059317753 219643271248948263044488315)
        ·
          refine ⟨329464906873422394566732473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219643271248948263044488315 329464906873422394566732473)
          ·
            refine ⟨247098680155066795925049355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329464906873422394566732473 247098680155066795925049355)
            ·
              refine ⟨370648020232600193887574033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247098680155066795925049355 370648020232600193887574033)
              ·
                refine ⟨277986015174450145415680525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370648020232600193887574033 277986015174450145415680525)
                ·
                  refine ⟨104244755690418804530880197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277986015174450145415680525 104244755690418804530880197)
                  ·
                    refine ⟨19545891691953525849540037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104244755690418804530880197 19545891691953525849540037)
                    ·
                      refine ⟨3664854692241286096788757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19545891691953525849540037 3664854692241286096788757)
                      ·
                        rfl

theorem cell23_7137279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_7137279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137279 prefixEnd_7137279 := by exact prefixLift 7137279
  have htrace : WordTrace (prefixWord ++ tailWord_7137279) baseStart_7137279 baseEnd_7137279 := by
    simpa [prefixWord, tailWord_7137279, baseEnd_7137279] using wordTrace_append hprefix tailTrace_7137279
  have hstable : (prefixWord ++ tailWord_7137279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137279).length < 2 ^ (prefixWord ++ tailWord_7137279).sum := by decide
  have hdescent : baseEnd_7137279 < baseStart_7137279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137283 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 4, 2, 2]
def baseStart_7137283 : Nat := 118140960795 + 7137283 * 2 ^ 59
def prefixEnd_7137283 : Nat := 4983230072969 + 3 ^ 40 * 7137283 * 2
def baseEnd_7137283 : Nat := 3664856746163904081138739

theorem tailTrace_7137283 : CollatzResearch.WordTrace tailWord_7137283 prefixEnd_7137283 3664856746163904081138739 := by
  unfold tailWord_7137283
  simp only [CollatzResearch.WordTrace]
  refine ⟨260318097001850116735872503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173545398001233411157248335 260318097001850116735872503)
  ·
    refine ⟨390477145502775175103808755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260318097001850116735872503 390477145502775175103808755)
    ·
      refine ⟨585715718254162762655713133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390477145502775175103808755 585715718254162762655713133)
      ·
        refine ⟨219643394345311035995892425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 585715718254162762655713133 219643394345311035995892425)
        ·
          refine ⟨164732545758983276996919319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219643394345311035995892425 164732545758983276996919319)
          ·
            refine ⟨247098818638474915495378979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164732545758983276996919319 247098818638474915495378979)
            ·
              refine ⟨370648227957712373243068469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247098818638474915495378979 370648227957712373243068469)
              ·
                refine ⟨34748271371035534991537669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 370648227957712373243068469 34748271371035534991537669)
                ·
                  refine ⟨6515300882069162810913313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34748271371035534991537669 6515300882069162810913313)
                  ·
                    refine ⟨4886475661551872108184985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6515300882069162810913313 4886475661551872108184985)
                    ·
                      refine ⟨3664856746163904081138739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4886475661551872108184985 3664856746163904081138739)
                      ·
                        rfl

theorem cell23_7137283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 2, 2].length) (baseStart_7137283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137283 prefixEnd_7137283 := by exact prefixLift 7137283
  have htrace : WordTrace (prefixWord ++ tailWord_7137283) baseStart_7137283 baseEnd_7137283 := by
    simpa [prefixWord, tailWord_7137283, baseEnd_7137283] using wordTrace_append hprefix tailTrace_7137283
  have hstable : (prefixWord ++ tailWord_7137283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137283).length < 2 ^ (prefixWord ++ tailWord_7137283).sum := by decide
  have hdescent : baseEnd_7137283 < baseStart_7137283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137306 : List Nat := [3, 1, 1, 3, 1, 4, 1, 2, 7]
def baseStart_7137306 : Nat := 118140960795 + 7137306 * 2 ^ 59
def prefixEnd_7137306 : Nat := 4983230072969 + 3 ^ 40 * 7137306 * 2
def baseEnd_7137306 : Nat := 407207617357661943461237

theorem tailTrace_7137306 : CollatzResearch.WordTrace tailWord_7137306 prefixEnd_7137306 407207617357661943461237 := by
  unfold tailWord_7137306
  simp only [CollatzResearch.WordTrace]
  refine ⟨65079733970191697915989943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173545957253844527775973181 65079733970191697915989943)
  ·
    refine ⟨97619600955287546873984915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65079733970191697915989943 97619600955287546873984915)
    ·
      refine ⟨146429401432931320310977373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97619600955287546873984915 146429401432931320310977373)
      ·
        refine ⟨54911025537349245116616515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146429401432931320310977373 54911025537349245116616515)
        ·
          refine ⟨82366538306023867674924773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54911025537349245116616515 82366538306023867674924773)
          ·
            refine ⟨15443725932379475189048395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82366538306023867674924773 15443725932379475189048395)
            ·
              refine ⟨23165588898569212783572593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15443725932379475189048395 23165588898569212783572593)
              ·
                refine ⟨17374191673926909587679445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23165588898569212783572593 17374191673926909587679445)
                ·
                  refine ⟨407207617357661943461237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17374191673926909587679445 407207617357661943461237)
                  ·
                    rfl

theorem cell23_7137306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 7].length) (baseStart_7137306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137306 prefixEnd_7137306 := by exact prefixLift 7137306
  have htrace : WordTrace (prefixWord ++ tailWord_7137306) baseStart_7137306 baseEnd_7137306 := by
    simpa [prefixWord, tailWord_7137306, baseEnd_7137306] using wordTrace_append hprefix tailTrace_7137306
  have hstable : (prefixWord ++ tailWord_7137306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137306).length < 2 ^ (prefixWord ++ tailWord_7137306).sum := by decide
  have hdescent : baseEnd_7137306 < baseStart_7137306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137350 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_7137350 : Nat := 118140960795 + 7137350 * 2 ^ 59
def prefixEnd_7137350 : Nat := 4983230072969 + 3 ^ 40 * 7137350 * 2
def baseEnd_7137350 : Nat := 3664891149367755319000931

theorem tailTrace_7137350 : CollatzResearch.WordTrace tailWord_7137350 prefixEnd_7137350 3664891149367755319000931 := by
  unfold tailWord_7137350
  simp only [CollatzResearch.WordTrace]
  refine ⟨8135016896643980849330047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 173547027128404924785707669 8135016896643980849330047)
  ·
    refine ⟨12202525344965971273995071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8135016896643980849330047 12202525344965971273995071)
    ·
      refine ⟨18303788017448956910992607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12202525344965971273995071 18303788017448956910992607)
      ·
        refine ⟨27455682026173435366488911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18303788017448956910992607 27455682026173435366488911)
        ·
          refine ⟨41183523039260153049733367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27455682026173435366488911 41183523039260153049733367)
          ·
            refine ⟨61775284558890229574600051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41183523039260153049733367 61775284558890229574600051)
            ·
              refine ⟨92662926838335344361900077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61775284558890229574600051 92662926838335344361900077)
              ·
                refine ⟨34748597564375754135712529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92662926838335344361900077 34748597564375754135712529)
                ·
                  refine ⟨26061448173281815601784397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34748597564375754135712529 26061448173281815601784397)
                  ·
                    refine ⟨9773043064980680850669149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26061448173281815601784397 9773043064980680850669149)
                    ·
                      refine ⟨3664891149367755319000931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9773043064980680850669149 3664891149367755319000931)
                      ·
                        rfl

theorem cell23_7137350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_7137350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137350 prefixEnd_7137350 := by exact prefixLift 7137350
  have htrace : WordTrace (prefixWord ++ tailWord_7137350) baseStart_7137350 baseEnd_7137350 := by
    simpa [prefixWord, tailWord_7137350, baseEnd_7137350] using wordTrace_append hprefix tailTrace_7137350
  have hstable : (prefixWord ++ tailWord_7137350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137350).length < 2 ^ (prefixWord ++ tailWord_7137350).sum := by decide
  have hdescent : baseEnd_7137350 < baseStart_7137350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137356 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 1, 3, 4]
def baseStart_7137356 : Nat := 118140960795 + 7137356 * 2 ^ 59
def prefixEnd_7137356 : Nat := 4983230072969 + 3 ^ 40 * 7137356 * 2
def baseEnd_7137356 : Nat := 3664894230251682295525903

theorem tailTrace_7137356 : CollatzResearch.WordTrace tailWord_7137356 prefixEnd_7137356 3664894230251682295525903 := by
  unfold tailWord_7137356
  simp only [CollatzResearch.WordTrace]
  refine ⟨130160379765292825101639961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173547173020390433468853281 130160379765292825101639961)
  ·
    refine ⟨97620284823969618826229971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130160379765292825101639961 97620284823969618826229971)
    ·
      refine ⟨146430427235954428239344957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97620284823969618826229971 146430427235954428239344957)
      ·
        refine ⟨54911410213482910589754359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146430427235954428239344957 54911410213482910589754359)
        ·
          refine ⟨82367115320224365884631539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54911410213482910589754359 82367115320224365884631539)
          ·
            refine ⟨123550672980336548826947309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82367115320224365884631539 123550672980336548826947309)
            ·
              refine ⟨46331502367626205810105241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123550672980336548826947309 46331502367626205810105241)
              ·
                refine ⟨34748626775719654357578931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46331502367626205810105241 34748626775719654357578931)
                ·
                  refine ⟨52122940163579481536368397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34748626775719654357578931 52122940163579481536368397)
                  ·
                    refine ⟨19546102561342305576138149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52122940163579481536368397 19546102561342305576138149)
                    ·
                      refine ⟨3664894230251682295525903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19546102561342305576138149 3664894230251682295525903)
                      ·
                        rfl

theorem cell23_7137356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_7137356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137356 prefixEnd_7137356 := by exact prefixLift 7137356
  have htrace : WordTrace (prefixWord ++ tailWord_7137356) baseStart_7137356 baseEnd_7137356 := by
    simpa [prefixWord, tailWord_7137356, baseEnd_7137356] using wordTrace_append hprefix tailTrace_7137356
  have hstable : (prefixWord ++ tailWord_7137356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137356).length < 2 ^ (prefixWord ++ tailWord_7137356).sum := by decide
  have hdescent : baseEnd_7137356 < baseStart_7137356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137393 : List Nat := [1, 2, 2, 2, 1, 1, 5, 2, 2, 2, 3]
def baseStart_7137393 : Nat := 118140960795 + 7137393 * 2 ^ 59
def prefixEnd_7137393 : Nat := 4983230072969 + 3 ^ 40 * 7137393 * 2
def baseEnd_7137393 : Nat := 3664913229035898650763233

theorem tailTrace_7137393 : CollatzResearch.WordTrace tailWord_7137393 prefixEnd_7137393 3664913229035898650763233 := by
  unfold tailWord_7137393
  simp only [CollatzResearch.WordTrace]
  refine ⟨260322109031451605522376833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173548072687634403681584555 260322109031451605522376833)
  ·
    refine ⟨195241581773588704141782625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260322109031451605522376833 195241581773588704141782625)
    ·
      refine ⟨146431186330191528106336969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195241581773588704141782625 146431186330191528106336969)
      ·
        refine ⟨109823389747643646079752727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146431186330191528106336969 109823389747643646079752727)
        ·
          refine ⟨164735084621465469119629091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109823389747643646079752727 164735084621465469119629091)
          ·
            refine ⟨247102626932198203679443637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164735084621465469119629091 247102626932198203679443637)
            ·
              refine ⟨23165871274893581594947841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 247102626932198203679443637 23165871274893581594947841)
              ·
                refine ⟨17374403456170186196210881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23165871274893581594947841 17374403456170186196210881)
                ·
                  refine ⟨13030802592127639647158161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17374403456170186196210881 13030802592127639647158161)
                  ·
                    refine ⟨9773101944095729735368621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13030802592127639647158161 9773101944095729735368621)
                    ·
                      refine ⟨3664913229035898650763233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9773101944095729735368621 3664913229035898650763233)
                      ·
                        rfl

theorem cell23_7137393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_7137393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137393 prefixEnd_7137393 := by exact prefixLift 7137393
  have htrace : WordTrace (prefixWord ++ tailWord_7137393) baseStart_7137393 baseEnd_7137393 := by
    simpa [prefixWord, tailWord_7137393, baseEnd_7137393] using wordTrace_append hprefix tailTrace_7137393
  have hstable : (prefixWord ++ tailWord_7137393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137393).length < 2 ^ (prefixWord ++ tailWord_7137393).sum := by decide
  have hdescent : baseEnd_7137393 < baseStart_7137393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137413 : List Nat := [1, 3, 1, 1, 5, 2, 1, 3, 6]
def baseStart_7137413 : Nat := 118140960795 + 7137413 * 2 ^ 59
def prefixEnd_7137413 : Nat := 4983230072969 + 3 ^ 40 * 7137413 * 2
def baseEnd_7137413 : Nat := 407213722072109841390349

theorem tailTrace_7137413 : CollatzResearch.WordTrace tailWord_7137413 prefixEnd_7137413 407213722072109841390349 := by
  unfold tailWord_7137413
  simp only [CollatzResearch.WordTrace]
  refine ⟨260322838491379148938104893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173548558994252765958736595 260322838491379148938104893)
  ·
    refine ⟨97621064434267180851789335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260322838491379148938104893 97621064434267180851789335)
    ·
      refine ⟨146431596651400771277684003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97621064434267180851789335 146431596651400771277684003)
      ·
        refine ⟨219647394977101156916526005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146431596651400771277684003 219647394977101156916526005)
        ·
          refine ⟨20591943279103233460924313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219647394977101156916526005 20591943279103233460924313)
          ·
            refine ⟨15443957459327425095693235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20591943279103233460924313 15443957459327425095693235)
            ·
              refine ⟨23165936188991137643539853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15443957459327425095693235 23165936188991137643539853)
              ·
                refine ⟨8687226070871676616327445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23165936188991137643539853 8687226070871676616327445)
                ·
                  refine ⟨407213722072109841390349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8687226070871676616327445 407213722072109841390349)
                  ·
                    rfl

theorem cell23_7137413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 6].length) (baseStart_7137413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137413 prefixEnd_7137413 := by exact prefixLift 7137413
  have htrace : WordTrace (prefixWord ++ tailWord_7137413) baseStart_7137413 baseEnd_7137413 := by
    simpa [prefixWord, tailWord_7137413, baseEnd_7137413] using wordTrace_append hprefix tailTrace_7137413
  have hstable : (prefixWord ++ tailWord_7137413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137413).length < 2 ^ (prefixWord ++ tailWord_7137413).sum := by decide
  have hdescent : baseEnd_7137413 < baseStart_7137413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137433 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 1, 5, 2]
def baseStart_7137433 : Nat := 118140960795 + 7137433 * 2 ^ 59
def prefixEnd_7137433 : Nat := 4983230072969 + 3 ^ 40 * 7137433 * 2
def baseEnd_7137433 : Nat := 3664933768262078494263049

theorem tailTrace_7137433 : CollatzResearch.WordTrace tailWord_7137433 prefixEnd_7137433 3664933768262078494263049 := by
  unfold tailWord_7137433
  simp only [CollatzResearch.WordTrace]
  refine ⟨260323567951306692353832953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173549045300871128235888635 260323567951306692353832953)
  ·
    refine ⟨195242675963480019265374715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260323567951306692353832953 195242675963480019265374715)
    ·
      refine ⟨292864013945220028898062073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195242675963480019265374715 292864013945220028898062073)
      ·
        refine ⟨219648010458915021673546555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292864013945220028898062073 219648010458915021673546555)
        ·
          refine ⟨329472015688372532510319833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219648010458915021673546555 329472015688372532510319833)
          ·
            refine ⟨247104011766279399382739875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329472015688372532510319833 247104011766279399382739875)
            ·
              refine ⟨370656017649419099074109813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247104011766279399382739875 370656017649419099074109813)
              ·
                refine ⟨34749001654633040538197795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 370656017649419099074109813 34749001654633040538197795)
                ·
                  refine ⟨52123502481949560807296693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34749001654633040538197795 52123502481949560807296693)
                  ·
                    refine ⟨4886578357682771325684065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52123502481949560807296693 4886578357682771325684065)
                    ·
                      refine ⟨3664933768262078494263049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4886578357682771325684065 3664933768262078494263049)
                      ·
                        rfl

theorem cell23_7137433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 5, 2].length) (baseStart_7137433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137433 prefixEnd_7137433 := by exact prefixLift 7137433
  have htrace : WordTrace (prefixWord ++ tailWord_7137433) baseStart_7137433 baseEnd_7137433 := by
    simpa [prefixWord, tailWord_7137433, baseEnd_7137433] using wordTrace_append hprefix tailTrace_7137433
  have hstable : (prefixWord ++ tailWord_7137433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137433).length < 2 ^ (prefixWord ++ tailWord_7137433).sum := by decide
  have hdescent : baseEnd_7137433 < baseStart_7137433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137463 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 4]
def baseStart_7137463 : Nat := 118140960795 + 7137463 * 2 ^ 59
def prefixEnd_7137463 : Nat := 4983230072969 + 3 ^ 40 * 7137463 * 2
def baseEnd_7137463 : Nat := 3664949172681713376887911

theorem tailTrace_7137463 : CollatzResearch.WordTrace tailWord_7137463 prefixEnd_7137463 3664949172681713376887911 := by
  unfold tailWord_7137463
  simp only [CollatzResearch.WordTrace]
  refine ⟨260324662141198007477425043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173549774760798671651616695 260324662141198007477425043)
  ·
    refine ⟨390486993211797011216137565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260324662141198007477425043 390486993211797011216137565)
    ·
      refine ⟨146432622454423879206051587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390486993211797011216137565 146432622454423879206051587)
      ·
        refine ⟨219648933681635818809077381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146432622454423879206051587 219648933681635818809077381)
        ·
          refine ⟨41184175065306716026702009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219648933681635818809077381 41184175065306716026702009)
          ·
            refine ⟨30888131298980037020026507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41184175065306716026702009 30888131298980037020026507)
            ·
              refine ⟨46332196948470055530039761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30888131298980037020026507 46332196948470055530039761)
              ·
                refine ⟨34749147711352541647529821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46332196948470055530039761 34749147711352541647529821)
                ·
                  refine ⟨13030930391757203117823683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34749147711352541647529821 13030930391757203117823683)
                  ·
                    refine ⟨19546395587635804676735525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13030930391757203117823683 19546395587635804676735525)
                    ·
                      refine ⟨3664949172681713376887911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19546395587635804676735525 3664949172681713376887911)
                      ·
                        rfl

theorem cell23_7137463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_7137463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137463 prefixEnd_7137463 := by exact prefixLift 7137463
  have htrace : WordTrace (prefixWord ++ tailWord_7137463) baseStart_7137463 baseEnd_7137463 := by
    simpa [prefixWord, tailWord_7137463, baseEnd_7137463] using wordTrace_append hprefix tailTrace_7137463
  have hstable : (prefixWord ++ tailWord_7137463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137463).length < 2 ^ (prefixWord ++ tailWord_7137463).sum := by decide
  have hdescent : baseEnd_7137463 < baseStart_7137463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137474 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_7137474 : Nat := 118140960795 + 7137474 * 2 ^ 59
def prefixEnd_7137474 : Nat := 4983230072969 + 3 ^ 40 * 7137474 * 2
def baseEnd_7137474 : Nat := 3664954820968912833850361

theorem tailTrace_7137474 : CollatzResearch.WordTrace tailWord_7137474 prefixEnd_7137474 3664954820968912833850361 := by
  unfold tailWord_7137474
  simp only [CollatzResearch.WordTrace]
  refine ⟨65081265836039539089018869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173550042229438770904050317 65081265836039539089018869)
  ·
    refine ⟨6101368672128706789595519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65081265836039539089018869 6101368672128706789595519)
    ·
      refine ⟨9152053008193060184393279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6101368672128706789595519 9152053008193060184393279)
      ·
        refine ⟨13728079512289590276589919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9152053008193060184393279 13728079512289590276589919)
        ·
          refine ⟨20592119268434385414884879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13728079512289590276589919 20592119268434385414884879)
          ·
            refine ⟨30888178902651578122327319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20592119268434385414884879 30888178902651578122327319)
            ·
              refine ⟨46332268353977367183490979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30888178902651578122327319 46332268353977367183490979)
              ·
                refine ⟨69498402530966050775236469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46332268353977367183490979 69498402530966050775236469)
                ·
                  refine ⟨6515475237278067260178419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69498402530966050775236469 6515475237278067260178419)
                  ·
                    refine ⟨9773212855917100890267629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6515475237278067260178419 9773212855917100890267629)
                    ·
                      refine ⟨3664954820968912833850361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9773212855917100890267629 3664954820968912833850361)
                      ·
                        rfl

theorem cell23_7137474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_7137474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137474 prefixEnd_7137474 := by exact prefixLift 7137474
  have htrace : WordTrace (prefixWord ++ tailWord_7137474) baseStart_7137474 baseEnd_7137474 := by
    simpa [prefixWord, tailWord_7137474, baseEnd_7137474] using wordTrace_append hprefix tailTrace_7137474
  have hstable : (prefixWord ++ tailWord_7137474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137474).length < 2 ^ (prefixWord ++ tailWord_7137474).sum := by decide
  have hdescent : baseEnd_7137474 < baseStart_7137474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137483 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 3]
def baseStart_7137483 : Nat := 118140960795 + 7137483 * 2 ^ 59
def prefixEnd_7137483 : Nat := 4983230072969 + 3 ^ 40 * 7137483 * 2
def baseEnd_7137483 : Nat := 3664959442294803298637819

theorem tailTrace_7137483 : CollatzResearch.WordTrace tailWord_7137483 prefixEnd_7137483 3664959442294803298637819 := by
  unfold tailWord_7137483
  simp only [CollatzResearch.WordTrace]
  refine ⟨260325391601125550893153103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173550261067417033928768735 260325391601125550893153103)
  ·
    refine ⟨390488087401688326339729655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260325391601125550893153103 390488087401688326339729655)
    ·
      refine ⟨585732131102532489509594483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390488087401688326339729655 585732131102532489509594483)
      ·
        refine ⟨878598196653798734264391725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585732131102532489509594483 878598196653798734264391725)
        ·
          refine ⟨329474323745174525349146897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 878598196653798734264391725 329474323745174525349146897)
          ·
            refine ⟨247105742808880894011860173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329474323745174525349146897 247105742808880894011860173)
            ·
              refine ⟨92664653553330335254447565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247105742808880894011860173 92664653553330335254447565)
              ·
                refine ⟨34749245082498875720417837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92664653553330335254447565 34749245082498875720417837)
                ·
                  refine ⟨13030966905937078395156689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34749245082498875720417837 13030966905937078395156689)
                  ·
                    refine ⟨9773225179452808796367517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13030966905937078395156689 9773225179452808796367517)
                    ·
                      refine ⟨3664959442294803298637819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9773225179452808796367517 3664959442294803298637819)
                      ·
                        rfl

theorem cell23_7137483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 3].length) (baseStart_7137483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137483 prefixEnd_7137483 := by exact prefixLift 7137483
  have htrace : WordTrace (prefixWord ++ tailWord_7137483) baseStart_7137483 baseEnd_7137483 := by
    simpa [prefixWord, tailWord_7137483, baseEnd_7137483] using wordTrace_append hprefix tailTrace_7137483
  have hstable : (prefixWord ++ tailWord_7137483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137483).length < 2 ^ (prefixWord ++ tailWord_7137483).sum := by decide
  have hdescent : baseEnd_7137483 < baseStart_7137483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137494 : List Nat := [5, 2, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_7137494 : Nat := 118140960795 + 7137494 * 2 ^ 59
def prefixEnd_7137494 : Nat := 4983230072969 + 3 ^ 40 * 7137494 * 2
def baseEnd_7137494 : Nat := 1221655030194000918533423

theorem tailTrace_7137494 : CollatzResearch.WordTrace tailWord_7137494 prefixEnd_7137494 1221655030194000918533423 := by
  unfold tailWord_7137494
  simp only [CollatzResearch.WordTrace]
  refine ⟨16270362050255356235737721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173550528536057133181202357 16270362050255356235737721)
  ·
    refine ⟨12202771537691517176803291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16270362050255356235737721 12202771537691517176803291)
    ·
      refine ⟨18304157306537275765204937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12202771537691517176803291 18304157306537275765204937)
      ·
        refine ⟨13728117979902956823903703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18304157306537275765204937 13728117979902956823903703)
        ·
          refine ⟨20592176969854435235855555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13728117979902956823903703 20592176969854435235855555)
          ·
            refine ⟨30888265454781652853783333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20592176969854435235855555 30888265454781652853783333)
            ·
              refine ⟨5791549772771559910084375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30888265454781652853783333 5791549772771559910084375)
              ·
                refine ⟨8687324659157339865126563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5791549772771559910084375 8687324659157339865126563)
                ·
                  refine ⟨13030986988736009797689845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8687324659157339865126563 13030986988736009797689845)
                  ·
                    refine ⟨1221655030194000918533423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13030986988736009797689845 1221655030194000918533423)
                    ·
                      rfl

theorem cell23_7137494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_7137494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137494 prefixEnd_7137494 := by exact prefixLift 7137494
  have htrace : WordTrace (prefixWord ++ tailWord_7137494) baseStart_7137494 baseEnd_7137494 := by
    simpa [prefixWord, tailWord_7137494, baseEnd_7137494] using wordTrace_append hprefix tailTrace_7137494
  have hstable : (prefixWord ++ tailWord_7137494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137494).length < 2 ^ (prefixWord ++ tailWord_7137494).sum := by decide
  have hdescent : baseEnd_7137494 < baseStart_7137494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137507 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 4, 4]
def baseStart_7137507 : Nat := 118140960795 + 7137507 * 2 ^ 59
def prefixEnd_7137507 : Nat := 4983230072969 + 3 ^ 40 * 7137507 * 2
def baseEnd_7137507 : Nat := 1221657255276837068245903

theorem tailTrace_7137507 : CollatzResearch.WordTrace tailWord_7137507 prefixEnd_7137507 1221657255276837068245903 := by
  unfold tailWord_7137507
  simp only [CollatzResearch.WordTrace]
  refine ⟨260326266953038602992026775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173550844635359068661351183 260326266953038602992026775)
  ·
    refine ⟨390489400429557904488040163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260326266953038602992026775 390489400429557904488040163)
    ·
      refine ⟨585734100644336856732060245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390489400429557904488040163 585734100644336856732060245)
      ·
        refine ⟨6864071491925822539828831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 585734100644336856732060245 6864071491925822539828831)
        ·
          refine ⟨10296107237888733809743247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6864071491925822539828831 10296107237888733809743247)
          ·
            refine ⟨15444160856833100714614871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10296107237888733809743247 15444160856833100714614871)
            ·
              refine ⟨23166241285249651071922307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15444160856833100714614871 23166241285249651071922307)
              ·
                refine ⟨34749361927874476607883461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23166241285249651071922307 34749361927874476607883461)
                ·
                  refine ⟨6515505361476464363978149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34749361927874476607883461 6515505361476464363978149)
                  ·
                    refine ⟨1221657255276837068245903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6515505361476464363978149 1221657255276837068245903)
                    ·
                      rfl

theorem cell23_7137507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 4].length) (baseStart_7137507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137507 prefixEnd_7137507 := by exact prefixLift 7137507
  have htrace : WordTrace (prefixWord ++ tailWord_7137507) baseStart_7137507 baseEnd_7137507 := by
    simpa [prefixWord, tailWord_7137507, baseEnd_7137507] using wordTrace_append hprefix tailTrace_7137507
  have hstable : (prefixWord ++ tailWord_7137507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137507).length < 2 ^ (prefixWord ++ tailWord_7137507).sum := by decide
  have hdescent : baseEnd_7137507 < baseStart_7137507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137514 : List Nat := [3, 1, 3, 1, 1, 2, 1, 6, 1, 2, 2]
def baseStart_7137514 : Nat := 118140960795 + 7137514 * 2 ^ 59
def prefixEnd_7137514 : Nat := 4983230072969 + 3 ^ 40 * 7137514 * 2
def baseEnd_7137514 : Nat := 3664975360195092677350177

theorem tailTrace_7137514 : CollatzResearch.WordTrace tailWord_7137514 prefixEnd_7137514 3664975360195092677350177 := by
  unfold tailWord_7137514
  simp only [CollatzResearch.WordTrace]
  refine ⟨65081630566003310796882899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173551014842675495458354397 65081630566003310796882899)
  ·
    refine ⟨97622445849004966195324349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65081630566003310796882899 97622445849004966195324349)
    ·
      refine ⟨36608417193376862323246631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97622445849004966195324349 36608417193376862323246631)
      ·
        refine ⟨54912625790065293484869947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36608417193376862323246631 54912625790065293484869947)
        ·
          refine ⟨82368938685097940227304921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54912625790065293484869947 82368938685097940227304921)
          ·
            refine ⟨61776704013823455170478691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82368938685097940227304921 61776704013823455170478691)
            ·
              refine ⟨92665056020735182755718037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61776704013823455170478691 92665056020735182755718037)
              ·
                refine ⟨4343674500971961691674283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92665056020735182755718037 4343674500971961691674283)
                ·
                  refine ⟨6515511751457942537511425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4343674500971961691674283 6515511751457942537511425)
                  ·
                    refine ⟨4886633813593456903133569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6515511751457942537511425 4886633813593456903133569)
                    ·
                      refine ⟨3664975360195092677350177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4886633813593456903133569 3664975360195092677350177)
                      ·
                        rfl

theorem cell23_7137514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_7137514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137514 prefixEnd_7137514 := by exact prefixLift 7137514
  have htrace : WordTrace (prefixWord ++ tailWord_7137514) baseStart_7137514 baseEnd_7137514 := by
    simpa [prefixWord, tailWord_7137514, baseEnd_7137514] using wordTrace_append hprefix tailTrace_7137514
  have hstable : (prefixWord ++ tailWord_7137514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137514).length < 2 ^ (prefixWord ++ tailWord_7137514).sum := by decide
  have hdescent : baseEnd_7137514 < baseStart_7137514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137530 : List Nat := [3, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3]
def baseStart_7137530 : Nat := 118140960795 + 7137530 * 2 ^ 59
def prefixEnd_7137530 : Nat := 4983230072969 + 3 ^ 40 * 7137530 * 2
def baseEnd_7137530 : Nat := 3664983575885564614750103

theorem tailTrace_7137530 : CollatzResearch.WordTrace tailWord_7137530 prefixEnd_7137530 3664983575885564614750103 := by
  unfold tailWord_7137530
  simp only [CollatzResearch.WordTrace]
  refine ⟨65081776457988819480028511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173551403887970185280076029 65081776457988819480028511)
  ·
    refine ⟨97622664686983229220042767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65081776457988819480028511 97622664686983229220042767)
    ·
      refine ⟨146433997030474843830064151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97622664686983229220042767 146433997030474843830064151)
      ·
        refine ⟨219650995545712265745096227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146433997030474843830064151 219650995545712265745096227)
        ·
          refine ⟨329476493318568398617644341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219650995545712265745096227 329476493318568398617644341)
          ·
            refine ⟨30888421248615787370404157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 329476493318568398617644341 30888421248615787370404157)
            ·
              refine ⟨11583157968230920263901559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30888421248615787370404157 11583157968230920263901559)
              ·
                refine ⟨17374736952346380395852339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11583157968230920263901559 17374736952346380395852339)
                ·
                  refine ⟨26062105428519570593778509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17374736952346380395852339 26062105428519570593778509)
                  ·
                    refine ⟨9773289535694838972666941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26062105428519570593778509 9773289535694838972666941)
                    ·
                      refine ⟨3664983575885564614750103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9773289535694838972666941 3664983575885564614750103)
                      ·
                        rfl

theorem cell23_7137530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_7137530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137530 prefixEnd_7137530 := by exact prefixLift 7137530
  have htrace : WordTrace (prefixWord ++ tailWord_7137530) baseStart_7137530 baseEnd_7137530 := by
    simpa [prefixWord, tailWord_7137530, baseEnd_7137530] using wordTrace_append hprefix tailTrace_7137530
  have hstable : (prefixWord ++ tailWord_7137530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137530).length < 2 ^ (prefixWord ++ tailWord_7137530).sum := by decide
  have hdescent : baseEnd_7137530 < baseStart_7137530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137557 : List Nat := [1, 3, 2, 1, 2, 1, 4, 3, 1, 3, 2]
def baseStart_7137557 : Nat := 118140960795 + 7137557 * 2 ^ 59
def prefixEnd_7137557 : Nat := 4983230072969 + 3 ^ 40 * 7137557 * 2
def baseEnd_7137557 : Nat := 3664997439863236009112479

theorem tailTrace_7137557 : CollatzResearch.WordTrace tailWord_7137557 prefixEnd_7137557 3664997439863236009112479 := by
  unfold tailWord_7137557
  simp only [CollatzResearch.WordTrace]
  refine ⟨260328090602857461531346925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173552060401904974354231283 260328090602857461531346925)
  ·
    refine ⟨97623033976071548074255097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260328090602857461531346925 97623033976071548074255097)
    ·
      refine ⟨73217275482053661055691323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97623033976071548074255097 73217275482053661055691323)
      ·
        refine ⟨109825913223080491583536985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73217275482053661055691323 109825913223080491583536985)
        ·
          refine ⟨82369434917310368687652739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109825913223080491583536985 82369434917310368687652739)
          ·
            refine ⟨123554152375965553031479109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82369434917310368687652739 123554152375965553031479109)
            ·
              refine ⟨23166403570493541193402333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123554152375965553031479109 23166403570493541193402333)
              ·
                refine ⟨8687401338935077947525875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23166403570493541193402333 8687401338935077947525875)
                ·
                  refine ⟨13031102008402616921288813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8687401338935077947525875 13031102008402616921288813)
                  ·
                    refine ⟨4886663253150981345483305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13031102008402616921288813 4886663253150981345483305)
                    ·
                      refine ⟨3664997439863236009112479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4886663253150981345483305 3664997439863236009112479)
                      ·
                        rfl

theorem cell23_7137557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_7137557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137557 prefixEnd_7137557 := by exact prefixLift 7137557
  have htrace : WordTrace (prefixWord ++ tailWord_7137557) baseStart_7137557 baseEnd_7137557 := by
    simpa [prefixWord, tailWord_7137557, baseEnd_7137557] using wordTrace_append hprefix tailTrace_7137557
  have hstable : (prefixWord ++ tailWord_7137557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137557).length < 2 ^ (prefixWord ++ tailWord_7137557).sum := by decide
  have hdescent : baseEnd_7137557 < baseStart_7137557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137575 : List Nat := [1, 1, 8, 1, 2, 1, 2, 1, 2, 4]
def baseStart_7137575 : Nat := 118140960795 + 7137575 * 2 ^ 59
def prefixEnd_7137575 : Nat := 4983230072969 + 3 ^ 40 * 7137575 * 2
def baseEnd_7137575 : Nat := 1221668894171672312895799

theorem tailTrace_7137575 : CollatzResearch.WordTrace tailWord_7137575 prefixEnd_7137575 1221668894171672312895799 := by
  unfold tailWord_7137575
  simp only [CollatzResearch.WordTrace]
  refine ⟨260328747116792250605502179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173552498077861500403668119 260328747116792250605502179)
  ·
    refine ⟨390493120675188375908253269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260328747116792250605502179 390493120675188375908253269)
    ·
      refine ⟨4576091257912363780174843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 390493120675188375908253269 4576091257912363780174843)
      ·
        refine ⟨6864136886868545670262265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4576091257912363780174843 6864136886868545670262265)
        ·
          refine ⟨5148102665151409252696699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6864136886868545670262265 5148102665151409252696699)
          ·
            refine ⟨7722153997727113879045049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5148102665151409252696699 7722153997727113879045049)
            ·
              refine ⟨5791615498295335409283787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7722153997727113879045049 5791615498295335409283787)
              ·
                refine ⟨8687423247443003113925681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5791615498295335409283787 8687423247443003113925681)
                ·
                  refine ⟨6515567435582252335444261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8687423247443003113925681 6515567435582252335444261)
                  ·
                    refine ⟨1221668894171672312895799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6515567435582252335444261 1221668894171672312895799)
                    ·
                      rfl

theorem cell23_7137575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_7137575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137575 prefixEnd_7137575 := by exact prefixLift 7137575
  have htrace : WordTrace (prefixWord ++ tailWord_7137575) baseStart_7137575 baseEnd_7137575 := by
    simpa [prefixWord, tailWord_7137575, baseEnd_7137575] using wordTrace_append hprefix tailTrace_7137575
  have hstable : (prefixWord ++ tailWord_7137575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137575).length < 2 ^ (prefixWord ++ tailWord_7137575).sum := by decide
  have hdescent : baseEnd_7137575 < baseStart_7137575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137581 : List Nat := [1, 5, 3, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_7137581 : Nat := 118140960795 + 7137581 * 2 ^ 59
def prefixEnd_7137581 : Nat := 4983230072969 + 3 ^ 40 * 7137581 * 2
def baseEnd_7137581 : Nat := 3665009763398943915212369

theorem tailTrace_7137581 : CollatzResearch.WordTrace tailWord_7137581 prefixEnd_7137581 3665009763398943915212369 := by
  unfold tailWord_7137581
  simp only [CollatzResearch.WordTrace]
  refine ⟨260328965954770513630220597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173552643969847009086813731 260328965954770513630220597)
  ·
    refine ⟨24405840558259735652833181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 260328965954770513630220597 24405840558259735652833181)
    ·
      refine ⟨9152190209347400869812443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24405840558259735652833181 9152190209347400869812443)
      ·
        refine ⟨13728285314021101304718665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9152190209347400869812443 13728285314021101304718665)
        ·
          refine ⟨10296213985515825978538999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13728285314021101304718665 10296213985515825978538999)
          ·
            refine ⟨15444320978273738967808499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10296213985515825978538999 15444320978273738967808499)
            ·
              refine ⟨23166481467410608451712749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15444320978273738967808499 23166481467410608451712749)
              ·
                refine ⟨8687430550278978169392281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23166481467410608451712749 8687430550278978169392281)
                ·
                  refine ⟨6515572912709233627044211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8687430550278978169392281 6515572912709233627044211)
                  ·
                    refine ⟨9773359369063850440566317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6515572912709233627044211 9773359369063850440566317)
                    ·
                      refine ⟨3665009763398943915212369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9773359369063850440566317 3665009763398943915212369)
                      ·
                        rfl

theorem cell23_7137581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_7137581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137581 prefixEnd_7137581 := by exact prefixLift 7137581
  have htrace : WordTrace (prefixWord ++ tailWord_7137581) baseStart_7137581 baseEnd_7137581 := by
    simpa [prefixWord, tailWord_7137581, baseEnd_7137581] using wordTrace_append hprefix tailTrace_7137581
  have hstable : (prefixWord ++ tailWord_7137581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137581).length < 2 ^ (prefixWord ++ tailWord_7137581).sum := by decide
  have hdescent : baseEnd_7137581 < baseStart_7137581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137583 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 4]
def baseStart_7137583 : Nat := 118140960795 + 7137583 * 2 ^ 59
def prefixEnd_7137583 : Nat := 4983230072969 + 3 ^ 40 * 7137583 * 2
def baseEnd_7137583 : Nat := 3665010790360252907387359

theorem tailTrace_7137583 : CollatzResearch.WordTrace tailWord_7137583 prefixEnd_7137583 3665010790360252907387359 := by
  unfold tailWord_7137583
  simp only [CollatzResearch.WordTrace]
  refine ⟨260329038900763267971793403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173552692600508845314528935 260329038900763267971793403)
  ·
    refine ⟨390493558351144901957690105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260329038900763267971793403 390493558351144901957690105)
    ·
      refine ⟨292870168763358676468267579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390493558351144901957690105 292870168763358676468267579)
      ·
        refine ⟨439305253145038014702401369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292870168763358676468267579 439305253145038014702401369)
        ·
          refine ⟨329478939858778511026801027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439305253145038014702401369 329478939858778511026801027)
          ·
            refine ⟨494218409788167766540201541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329478939858778511026801027 494218409788167766540201541)
            ·
              refine ⟨92665951835281456226287789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 494218409788167766540201541 92665951835281456226287789)
              ·
                refine ⟨34749731938230546084857921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92665951835281456226287789 34749731938230546084857921)
                ·
                  refine ⟨26062298953672909563643441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34749731938230546084857921 26062298953672909563643441)
                  ·
                    refine ⟨19546724215254682172732581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26062298953672909563643441 19546724215254682172732581)
                    ·
                      refine ⟨3665010790360252907387359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19546724215254682172732581 3665010790360252907387359)
                      ·
                        rfl

theorem cell23_7137583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_7137583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137583 prefixEnd_7137583 := by exact prefixLift 7137583
  have htrace : WordTrace (prefixWord ++ tailWord_7137583) baseStart_7137583 baseEnd_7137583 := by
    simpa [prefixWord, tailWord_7137583, baseEnd_7137583] using wordTrace_append hprefix tailTrace_7137583
  have hstable : (prefixWord ++ tailWord_7137583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137583).length < 2 ^ (prefixWord ++ tailWord_7137583).sum := by decide
  have hdescent : baseEnd_7137583 < baseStart_7137583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137621 : List Nat := [1, 3, 2, 2, 4, 1, 2, 2, 2, 2, 2]
def baseStart_7137621 : Nat := 118140960795 + 7137621 * 2 ^ 59
def prefixEnd_7137621 : Nat := 4983230072969 + 3 ^ 40 * 7137621 * 2
def baseEnd_7137621 : Nat := 3665030302625123758712185

theorem tailTrace_7137621 : CollatzResearch.WordTrace tailWord_7137621 prefixEnd_7137621 3665030302625123758712185 := by
  unfold tailWord_7137621
  simp only [CollatzResearch.WordTrace]
  refine ⟨260330424874625600461676717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173553616583083733641117811 260330424874625600461676717)
  ·
    refine ⟨97623909327984600173128769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260330424874625600461676717 97623909327984600173128769)
    ·
      refine ⟨73217931995988450129846577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97623909327984600173128769 73217931995988450129846577)
      ·
        refine ⟨54913448996991337597384933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73217931995988450129846577 54913448996991337597384933)
        ·
          refine ⟨10296271686935875799509675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54913448996991337597384933 10296271686935875799509675)
          ·
            refine ⟨15444407530403813699264513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10296271686935875799509675 15444407530403813699264513)
            ·
              refine ⟨11583305647802860274448385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15444407530403813699264513 11583305647802860274448385)
              ·
                refine ⟨8687479235852145205836289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11583305647802860274448385 8687479235852145205836289)
                ·
                  refine ⟨6515609426889108904377217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8687479235852145205836289 6515609426889108904377217)
                  ·
                    refine ⟨4886707070166831678282913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6515609426889108904377217 4886707070166831678282913)
                    ·
                      refine ⟨3665030302625123758712185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4886707070166831678282913 3665030302625123758712185)
                      ·
                        rfl

theorem cell23_7137621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_7137621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137621 prefixEnd_7137621 := by exact prefixLift 7137621
  have htrace : WordTrace (prefixWord ++ tailWord_7137621) baseStart_7137621 baseEnd_7137621 := by
    simpa [prefixWord, tailWord_7137621, baseEnd_7137621] using wordTrace_append hprefix tailTrace_7137621
  have hstable : (prefixWord ++ tailWord_7137621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137621).length < 2 ^ (prefixWord ++ tailWord_7137621).sum := by decide
  have hdescent : baseEnd_7137621 < baseStart_7137621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137643 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4]
def baseStart_7137643 : Nat := 118140960795 + 7137643 * 2 ^ 59
def prefixEnd_7137643 : Nat := 4983230072969 + 3 ^ 40 * 7137643 * 2
def baseEnd_7137643 : Nat := 3665041599199522672637083

theorem tailTrace_7137643 : CollatzResearch.WordTrace tailWord_7137643 prefixEnd_7137643 3665041599199522672637083 := by
  unfold tailWord_7137643
  simp only [CollatzResearch.WordTrace]
  refine ⟨260331227280545898218977583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173554151520363932145985055 260331227280545898218977583)
  ·
    refine ⟨390496840920818847328466375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260331227280545898218977583 390496840920818847328466375)
    ·
      refine ⟨585745261381228270992699563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390496840920818847328466375 585745261381228270992699563)
      ·
        refine ⟨878617892071842406489049345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585745261381228270992699563 878617892071842406489049345)
        ·
          refine ⟨658963419053881804866787009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 878617892071842406489049345 658963419053881804866787009)
          ·
            refine ⟨494222564290411353650090257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658963419053881804866787009 494222564290411353650090257)
            ·
              refine ⟨370666923217808515237567693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494222564290411353650090257 370666923217808515237567693)
              ·
                refine ⟨139000096206678193214087885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370666923217808515237567693 139000096206678193214087885)
                ·
                  refine ⟨52125036077504322455282957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139000096206678193214087885 52125036077504322455282957)
                  ·
                    refine ⟨19546888529064120920731109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52125036077504322455282957 19546888529064120920731109)
                    ·
                      refine ⟨3665041599199522672637083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19546888529064120920731109 3665041599199522672637083)
                      ·
                        rfl

theorem cell23_7137643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4].length) (baseStart_7137643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137643 prefixEnd_7137643 := by exact prefixLift 7137643
  have htrace : WordTrace (prefixWord ++ tailWord_7137643) baseStart_7137643 baseEnd_7137643 := by
    simpa [prefixWord, tailWord_7137643, baseEnd_7137643] using wordTrace_append hprefix tailTrace_7137643
  have hstable : (prefixWord ++ tailWord_7137643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137643).length < 2 ^ (prefixWord ++ tailWord_7137643).sum := by decide
  have hdescent : baseEnd_7137643 < baseStart_7137643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137660 : List Nat := [2, 2, 2, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_7137660 : Nat := 118140960795 + 7137660 * 2 ^ 59
def prefixEnd_7137660 : Nat := 4983230072969 + 3 ^ 40 * 7137660 * 2
def baseEnd_7137660 : Nat := 3665050328370649106124505

theorem tailTrace_7137660 : CollatzResearch.WordTrace tailWord_7137660 prefixEnd_7137660 3665050328370649106124505 := by
  unfold tailWord_7137660
  simp only [CollatzResearch.WordTrace]
  refine ⟨130165923660742155061173217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173554564880989540081564289 130165923660742155061173217)
  ·
    refine ⟨97624442745556616295879913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130165923660742155061173217 97624442745556616295879913)
    ·
      refine ⟨73218332059167462221909935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97624442745556616295879913 73218332059167462221909935)
      ·
        refine ⟨109827498088751193332864903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73218332059167462221909935 109827498088751193332864903)
        ·
          refine ⟨164741247133126789999297355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109827498088751193332864903 164741247133126789999297355)
          ·
            refine ⟨247111870699690184998946033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164741247133126789999297355 247111870699690184998946033)
            ·
              refine ⟨185333903024767638749209525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247111870699690184998946033 185333903024767638749209525)
              ·
                refine ⟨17375053408571966132738393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185333903024767638749209525 17375053408571966132738393)
                ·
                  refine ⟨13031290056428974599553795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17375053408571966132738393 13031290056428974599553795)
                  ·
                    refine ⟨19546935084643461899330693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13031290056428974599553795 19546935084643461899330693)
                    ·
                      refine ⟨3665050328370649106124505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19546935084643461899330693 3665050328370649106124505)
                      ·
                        rfl

theorem cell23_7137660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_7137660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137660 prefixEnd_7137660 := by exact prefixLift 7137660
  have htrace : WordTrace (prefixWord ++ tailWord_7137660) baseStart_7137660 baseEnd_7137660 := by
    simpa [prefixWord, tailWord_7137660, baseEnd_7137660] using wordTrace_append hprefix tailTrace_7137660
  have hstable : (prefixWord ++ tailWord_7137660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137660).length < 2 ^ (prefixWord ++ tailWord_7137660).sum := by decide
  have hdescent : baseEnd_7137660 < baseStart_7137660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137700 : List Nat := [2, 3, 1, 2, 1, 1, 2, 5, 6]
def baseStart_7137700 : Nat := 118140960795 + 7137700 * 2 ^ 59
def prefixEnd_7137700 : Nat := 4983230072969 + 3 ^ 40 * 7137700 * 2
def baseEnd_7137700 : Nat := 407230096399647661069369

theorem tailTrace_7137700 : CollatzResearch.WordTrace tailWord_7137700 prefixEnd_7137700 407230096399647661069369 := by
  unfold tailWord_7137700
  simp only [CollatzResearch.WordTrace]
  refine ⟨130166653120669698476901277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173555537494226264635868369 130166653120669698476901277)
  ·
    refine ⟨48812494920251136928837979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130166653120669698476901277 48812494920251136928837979)
    ·
      refine ⟨73218742380376705393256969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48812494920251136928837979 73218742380376705393256969)
      ·
        refine ⟨54914056785282529044942727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73218742380376705393256969 54914056785282529044942727)
        ·
          refine ⟨82371085177923793567414091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54914056785282529044942727 82371085177923793567414091)
          ·
            refine ⟨123556627766885690351121137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82371085177923793567414091 123556627766885690351121137)
            ·
              refine ⟨92667470825164267763340853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123556627766885690351121137 92667470825164267763340853)
              ·
                refine ⟨8687575389859150102813205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92667470825164267763340853 8687575389859150102813205)
                ·
                  refine ⟨407230096399647661069369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8687575389859150102813205 407230096399647661069369)
                  ·
                    rfl

theorem cell23_7137700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_7137700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137700 prefixEnd_7137700 := by exact prefixLift 7137700
  have htrace : WordTrace (prefixWord ++ tailWord_7137700) baseStart_7137700 baseEnd_7137700 := by
    simpa [prefixWord, tailWord_7137700, baseEnd_7137700] using wordTrace_append hprefix tailTrace_7137700
  have hstable : (prefixWord ++ tailWord_7137700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137700).length < 2 ^ (prefixWord ++ tailWord_7137700).sum := by decide
  have hdescent : baseEnd_7137700 < baseStart_7137700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137704 : List Nat := [2, 1, 6, 1, 1, 1, 2, 2, 3, 4]
def baseStart_7137704 : Nat := 118140960795 + 7137704 * 2 ^ 59
def prefixEnd_7137704 : Nat := 4983230072969 + 3 ^ 40 * 7137704 * 2
def baseEnd_7137704 : Nat := 1221690973839815644658101

theorem tailTrace_7137704 : CollatzResearch.WordTrace tailWord_7137704 prefixEnd_7137704 1221690973839815644658101 := by
  unfold tailWord_7137704
  simp only [CollatzResearch.WordTrace]
  refine ⟨130166726066662452818474083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173555634755549937091298777 130166726066662452818474083)
  ·
    refine ⟨195250089099993679227711125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130166726066662452818474083 195250089099993679227711125)
    ·
      refine ⟨9152347926562203713798959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 195250089099993679227711125 9152347926562203713798959)
      ·
        refine ⟨13728521889843305570698439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9152347926562203713798959 13728521889843305570698439)
        ·
          refine ⟨20592782834764958356047659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13728521889843305570698439 20592782834764958356047659)
          ·
            refine ⟨30889174252147437534071489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20592782834764958356047659 30889174252147437534071489)
            ·
              refine ⟨23166880689110578150553617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30889174252147437534071489 23166880689110578150553617)
              ·
                refine ⟨17375160516832933612915213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23166880689110578150553617 17375160516832933612915213)
                ·
                  refine ⟨6515685193812350104843205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17375160516832933612915213 6515685193812350104843205)
                  ·
                    refine ⟨1221690973839815644658101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6515685193812350104843205 1221690973839815644658101)
                    ·
                      rfl

theorem cell23_7137704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_7137704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137704 prefixEnd_7137704 := by exact prefixLift 7137704
  have htrace : WordTrace (prefixWord ++ tailWord_7137704) baseStart_7137704 baseEnd_7137704 := by
    simpa [prefixWord, tailWord_7137704, baseEnd_7137704] using wordTrace_append hprefix tailTrace_7137704
  have hstable : (prefixWord ++ tailWord_7137704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137704).length < 2 ^ (prefixWord ++ tailWord_7137704).sum := by decide
  have hdescent : baseEnd_7137704 < baseStart_7137704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137721 : List Nat := [1, 2, 1, 4, 3, 3, 1, 3, 1, 4]
def baseStart_7137721 : Nat := 118140960795 + 7137721 * 2 ^ 59
def prefixEnd_7137721 : Nat := 4983230072969 + 3 ^ 40 * 7137721 * 2
def baseEnd_7137721 : Nat := 1221693883563524455820575

theorem tailTrace_7137721 : CollatzResearch.WordTrace tailWord_7137721 prefixEnd_7137721 1221693883563524455820575 := by
  unfold tailWord_7137721
  simp only [CollatzResearch.WordTrace]
  refine ⟨260334072174263317540317017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173556048116175545026878011 260334072174263317540317017)
  ·
    refine ⟨195250554130697488155237763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260334072174263317540317017 195250554130697488155237763)
    ·
      refine ⟨292875831196046232232856645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195250554130697488155237763 292875831196046232232856645)
      ·
        refine ⟨54914218349258668543660621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292875831196046232232856645 54914218349258668543660621)
        ·
          refine ⟨20592831880972000703872733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54914218349258668543660621 20592831880972000703872733)
          ·
            refine ⟨7722311955364500263952275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20592831880972000703872733 7722311955364500263952275)
            ·
              refine ⟨11583467933046750395928413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7722311955364500263952275 11583467933046750395928413)
              ·
                refine ⟨4343800474892531398473155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11583467933046750395928413 4343800474892531398473155)
                ·
                  refine ⟨6515700712338797097709733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4343800474892531398473155 6515700712338797097709733)
                  ·
                    refine ⟨1221693883563524455820575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6515700712338797097709733 1221693883563524455820575)
                    ·
                      rfl

theorem cell23_7137721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 1, 4].length) (baseStart_7137721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137721 prefixEnd_7137721 := by exact prefixLift 7137721
  have htrace : WordTrace (prefixWord ++ tailWord_7137721) baseStart_7137721 baseEnd_7137721 := by
    simpa [prefixWord, tailWord_7137721, baseEnd_7137721] using wordTrace_append hprefix tailTrace_7137721
  have hstable : (prefixWord ++ tailWord_7137721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137721).length < 2 ^ (prefixWord ++ tailWord_7137721).sum := by decide
  have hdescent : baseEnd_7137721 < baseStart_7137721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137723 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 7]
def baseStart_7137723 : Nat := 118140960795 + 7137723 * 2 ^ 59
def prefixEnd_7137723 : Nat := 4983230072969 + 3 ^ 40 * 7137723 * 2
def baseEnd_7137723 : Nat := 3665082677651882359636715

theorem tailTrace_7137723 : CollatzResearch.WordTrace tailWord_7137723 prefixEnd_7137723 3665082677651882359636715 := by
  unfold tailWord_7137723
  simp only [CollatzResearch.WordTrace]
  refine ⟨260334145120256071881889823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173556096746837381254593215 260334145120256071881889823)
  ·
    refine ⟨390501217680384107822834735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260334145120256071881889823 390501217680384107822834735)
    ·
      refine ⟨585751826520576161734252103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390501217680384107822834735 585751826520576161734252103)
      ·
        refine ⟨878627739780864242601378155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585751826520576161734252103 878627739780864242601378155)
        ·
          refine ⟨1317941609671296363902067233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878627739780864242601378155 1317941609671296363902067233)
          ·
            refine ⟨988456207253472272926550425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1317941609671296363902067233 988456207253472272926550425)
            ·
              refine ⟨741342155440104204694912819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988456207253472272926550425 741342155440104204694912819)
              ·
                refine ⟨1112013233160156307042369229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741342155440104204694912819 1112013233160156307042369229)
                ·
                  refine ⟨417004962435058615140888461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112013233160156307042369229 417004962435058615140888461)
                  ·
                    refine ⟨156376860913146980677833173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 417004962435058615140888461 156376860913146980677833173)
                    ·
                      refine ⟨3665082677651882359636715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156376860913146980677833173 3665082677651882359636715)
                      ·
                        rfl

theorem cell23_7137723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 7].length) (baseStart_7137723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137723 prefixEnd_7137723 := by exact prefixLift 7137723
  have htrace : WordTrace (prefixWord ++ tailWord_7137723) baseStart_7137723 baseEnd_7137723 := by
    simpa [prefixWord, tailWord_7137723, baseEnd_7137723] using wordTrace_append hprefix tailTrace_7137723
  have hstable : (prefixWord ++ tailWord_7137723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137723).length < 2 ^ (prefixWord ++ tailWord_7137723).sum := by decide
  have hdescent : baseEnd_7137723 < baseStart_7137723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137737 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 4, 3, 2]
def baseStart_7137737 : Nat := 118140960795 + 7137737 * 2 ^ 59
def prefixEnd_7137737 : Nat := 4983230072969 + 3 ^ 40 * 7137737 * 2
def baseEnd_7137737 : Nat := 3665089866381045304861651

theorem tailTrace_7137737 : CollatzResearch.WordTrace tailWord_7137737 prefixEnd_7137737 3665089866381045304861651 := by
  unfold tailWord_7137737
  simp only [CollatzResearch.WordTrace]
  refine ⟨260334655742205352272899465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173556437161470234848599643 260334655742205352272899465)
  ·
    refine ⟨195250991806654014204674599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260334655742205352272899465 195250991806654014204674599)
    ·
      refine ⟨292876487709981021307011899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195250991806654014204674599 292876487709981021307011899)
      ·
        refine ⟨439314731564971531960517849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292876487709981021307011899 439314731564971531960517849)
        ·
          refine ⟨329486048673728648970388387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439314731564971531960517849 329486048673728648970388387)
          ·
            refine ⟨494229073010592973455582581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329486048673728648970388387 494229073010592973455582581)
            ·
              refine ⟨46333975594743091261460867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 494229073010592973455582581 46333975594743091261460867)
              ·
                refine ⟨69500963392114636892191301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46333975594743091261460867 69500963392114636892191301)
                ·
                  refine ⟨13031430636021494417285869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69500963392114636892191301 13031430636021494417285869)
                  ·
                    refine ⟨4886786488508060406482201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13031430636021494417285869 4886786488508060406482201)
                    ·
                      refine ⟨3665089866381045304861651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4886786488508060406482201 3665089866381045304861651)
                      ·
                        rfl

theorem cell23_7137737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 3, 2].length) (baseStart_7137737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137737 prefixEnd_7137737 := by exact prefixLift 7137737
  have htrace : WordTrace (prefixWord ++ tailWord_7137737) baseStart_7137737 baseEnd_7137737 := by
    simpa [prefixWord, tailWord_7137737, baseEnd_7137737] using wordTrace_append hprefix tailTrace_7137737
  have hstable : (prefixWord ++ tailWord_7137737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137737).length < 2 ^ (prefixWord ++ tailWord_7137737).sum := by decide
  have hdescent : baseEnd_7137737 < baseStart_7137737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137760 : List Nat := [2, 1, 1, 3, 1, 1, 4, 3, 1, 6]
def baseStart_7137760 : Nat := 118140960795 + 7137760 * 2 ^ 59
def prefixEnd_7137760 : Nat := 4983230072969 + 3 ^ 40 * 7137760 * 2
def baseEnd_7137760 : Nat := 1221700558812032904958015

theorem tailTrace_7137760 : CollatzResearch.WordTrace tailWord_7137760 prefixEnd_7137760 1221700558812032904958015 := by
  unfold tailWord_7137760
  simp only [CollatzResearch.WordTrace]
  refine ⟨130167747310561013600493367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173556996414081351467324489 130167747310561013600493367)
  ·
    refine ⟨195251620965841520400740051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130167747310561013600493367 195251620965841520400740051)
    ·
      refine ⟨292877431448762280601110077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195251620965841520400740051 292877431448762280601110077)
      ·
        refine ⟨109829036793285855225416279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292877431448762280601110077 109829036793285855225416279)
        ·
          refine ⟨164743555189928782838124419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109829036793285855225416279 164743555189928782838124419)
          ·
            refine ⟨247115332784893174257186629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164743555189928782838124419 247115332784893174257186629)
            ·
              refine ⟨46334124897167470173222493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247115332784893174257186629 46334124897167470173222493)
              ·
                refine ⟨17375296836437801314958435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46334124897167470173222493 17375296836437801314958435)
                ·
                  refine ⟨26062945254656701972437653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17375296836437801314958435 26062945254656701972437653)
                  ·
                    refine ⟨1221700558812032904958015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26062945254656701972437653 1221700558812032904958015)
                    ·
                      rfl

theorem cell23_7137760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 1, 6].length) (baseStart_7137760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137760 prefixEnd_7137760 := by exact prefixLift 7137760
  have htrace : WordTrace (prefixWord ++ tailWord_7137760) baseStart_7137760 baseEnd_7137760 := by
    simpa [prefixWord, tailWord_7137760, baseEnd_7137760] using wordTrace_append hprefix tailTrace_7137760
  have hstable : (prefixWord ++ tailWord_7137760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137760).length < 2 ^ (prefixWord ++ tailWord_7137760).sum := by decide
  have hdescent : baseEnd_7137760 < baseStart_7137760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137767 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_7137767 : Nat := 118140960795 + 7137767 * 2 ^ 59
def prefixEnd_7137767 : Nat := 4983230072969 + 3 ^ 40 * 7137767 * 2
def baseEnd_7137767 : Nat := 3665105270800680187486513

theorem tailTrace_7137767 : CollatzResearch.WordTrace tailWord_7137767 prefixEnd_7137767 3665105270800680187486513 := by
  unfold tailWord_7137767
  simp only [CollatzResearch.WordTrace]
  refine ⟨260335749932096667396491555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173557166621397778264327703 260335749932096667396491555)
  ·
    refine ⟨390503624898145001094737333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260335749932096667396491555 390503624898145001094737333)
    ·
      refine ⟨36609714834201093852631625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 390503624898145001094737333 36609714834201093852631625)
      ·
        refine ⟨27457286125650820389473719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36609714834201093852631625 27457286125650820389473719)
        ·
          refine ⟨41185929188476230584210579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27457286125650820389473719 41185929188476230584210579)
          ·
            refine ⟨61778893782714345876315869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41185929188476230584210579 61778893782714345876315869)
            ·
              refine ⟨23167085168517879703618451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61778893782714345876315869 23167085168517879703618451)
              ·
                refine ⟨34750627752776819555427677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23167085168517879703618451 34750627752776819555427677)
                ·
                  refine ⟨13031485407291307333285379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34750627752776819555427677 13031485407291307333285379)
                  ·
                    refine ⟨19547228110936960999928069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13031485407291307333285379 19547228110936960999928069)
                    ·
                      refine ⟨3665105270800680187486513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19547228110936960999928069 3665105270800680187486513)
                      ·
                        rfl

theorem cell23_7137767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_7137767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137767 prefixEnd_7137767 := by exact prefixLift 7137767
  have htrace : WordTrace (prefixWord ++ tailWord_7137767) baseStart_7137767 baseEnd_7137767 := by
    simpa [prefixWord, tailWord_7137767, baseEnd_7137767] using wordTrace_append hprefix tailTrace_7137767
  have hstable : (prefixWord ++ tailWord_7137767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137767).length < 2 ^ (prefixWord ++ tailWord_7137767).sum := by decide
  have hdescent : baseEnd_7137767 < baseStart_7137767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137784 : List Nat := [2, 1, 2, 1, 1, 4, 5, 1, 1, 1, 4]
def baseStart_7137784 : Nat := 118140960795 + 7137784 * 2 ^ 59
def prefixEnd_7137784 : Nat := 4983230072969 + 3 ^ 40 * 7137784 * 2
def baseEnd_7137784 : Nat := 3665113999971806620973935

theorem tailTrace_7137784 : CollatzResearch.WordTrace tailWord_7137784 prefixEnd_7137784 3665113999971806620973935 := by
  unfold tailWord_7137784
  simp only [CollatzResearch.WordTrace]
  refine ⟨130168184986517539649930203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173557579982023386199906937 130168184986517539649930203)
  ·
    refine ⟨195252277479776309474895305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130168184986517539649930203 195252277479776309474895305)
    ·
      refine ⟨146439208109832232106171479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195252277479776309474895305 146439208109832232106171479)
      ·
        refine ⟨219658812164748348159257219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146439208109832232106171479 219658812164748348159257219)
        ·
          refine ⟨329488218247122522238885829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219658812164748348159257219 329488218247122522238885829)
          ·
            refine ⟨61779040921335472919791093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 329488218247122522238885829 61779040921335472919791093)
            ·
              refine ⟨5791785086375200586230415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61779040921335472919791093 5791785086375200586230415)
              ·
                refine ⟨8687677629562800879345623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5791785086375200586230415 8687677629562800879345623)
                ·
                  refine ⟨13031516444344201319018435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8687677629562800879345623 13031516444344201319018435)
                  ·
                    refine ⟨19547274666516301978527653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13031516444344201319018435 19547274666516301978527653)
                    ·
                      refine ⟨3665113999971806620973935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19547274666516301978527653 3665113999971806620973935)
                      ·
                        rfl

theorem cell23_7137784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 1, 1, 4].length) (baseStart_7137784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137784 prefixEnd_7137784 := by exact prefixLift 7137784
  have htrace : WordTrace (prefixWord ++ tailWord_7137784) baseStart_7137784 baseEnd_7137784 := by
    simpa [prefixWord, tailWord_7137784, baseEnd_7137784] using wordTrace_append hprefix tailTrace_7137784
  have hstable : (prefixWord ++ tailWord_7137784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137784).length < 2 ^ (prefixWord ++ tailWord_7137784).sum := by decide
  have hdescent : baseEnd_7137784 < baseStart_7137784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137790 : List Nat := [4, 2, 2, 15]
def baseStart_7137790 : Nat := 118140960795 + 7137790 * 2 ^ 59
def prefixEnd_7137790 : Nat := 4983230072969 + 3 ^ 40 * 7137790 * 2
def baseEnd_7137790 : Nat := 1675865148996677456561

theorem tailTrace_7137790 : CollatzResearch.WordTrace tailWord_7137790 prefixEnd_7137790 1675865148996677456561 := by
  unfold tailWord_7137790
  simp only [CollatzResearch.WordTrace]
  refine ⟨32542073601376667790572353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173557725874008894883052549 32542073601376667790572353)
  ·
    refine ⟨24406555201032500842929265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32542073601376667790572353 24406555201032500842929265)
    ·
      refine ⟨18304916400774375632196949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24406555201032500842929265 18304916400774375632196949)
      ·
        refine ⟨1675865148996677456561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 18304916400774375632196949 1675865148996677456561)
        ·
          rfl

theorem cell23_7137790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 15].length) (baseStart_7137790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137790 prefixEnd_7137790 := by exact prefixLift 7137790
  have htrace : WordTrace (prefixWord ++ tailWord_7137790) baseStart_7137790 baseEnd_7137790 := by
    simpa [prefixWord, tailWord_7137790, baseEnd_7137790] using wordTrace_append hprefix tailTrace_7137790
  have hstable : (prefixWord ++ tailWord_7137790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137790).length < 2 ^ (prefixWord ++ tailWord_7137790).sum := by decide
  have hdescent : baseEnd_7137790 < baseStart_7137790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137824 : List Nat := [2, 1, 1, 6, 2, 1, 3, 7]
def baseStart_7137824 : Nat := 118140960795 + 7137824 * 2 ^ 59
def prefixEnd_7137824 : Nat := 4983230072969 + 3 ^ 40 * 7137824 * 2
def baseEnd_7137824 : Nat := 135745723673999498684213

theorem tailTrace_7137824 : CollatzResearch.WordTrace tailWord_7137824 prefixEnd_7137824 135745723673999498684213 := by
  unfold tailWord_7137824
  simp only [CollatzResearch.WordTrace]
  refine ⟨130168914446445083065658263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173558552595260110754211017 130168914446445083065658263)
  ·
    refine ⟨195253371669667624598487395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130168914446445083065658263 195253371669667624598487395)
    ·
      refine ⟨292880057504501436897731093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195253371669667624598487395 292880057504501436897731093)
      ·
        refine ⟨13728752695523504854581145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 292880057504501436897731093 13728752695523504854581145)
        ·
          refine ⟨10296564521642628640935859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13728752695523504854581145 10296564521642628640935859)
          ·
            refine ⟨15444846782463942961403789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10296564521642628640935859 15444846782463942961403789)
            ·
              refine ⟨5791817543423978610526421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15444846782463942961403789 5791817543423978610526421)
              ·
                refine ⟨135745723673999498684213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5791817543423978610526421 135745723673999498684213)
                ·
                  rfl

theorem cell23_7137824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 7].length) (baseStart_7137824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137824 prefixEnd_7137824 := by exact prefixLift 7137824
  have htrace : WordTrace (prefixWord ++ tailWord_7137824) baseStart_7137824 baseEnd_7137824 := by
    simpa [prefixWord, tailWord_7137824, baseEnd_7137824] using wordTrace_append hprefix tailTrace_7137824
  have hstable : (prefixWord ++ tailWord_7137824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137824).length < 2 ^ (prefixWord ++ tailWord_7137824).sum := by decide
  have hdescent : baseEnd_7137824 < baseStart_7137824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137834 : List Nat := [3, 1, 4, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_7137834 : Nat := 118140960795 + 7137834 * 2 ^ 59
def prefixEnd_7137834 : Nat := 4983230072969 + 3 ^ 40 * 7137834 * 2
def baseEnd_7137834 : Nat := 3665139674004531425348705

theorem tailTrace_7137834 : CollatzResearch.WordTrace tailWord_7137834 prefixEnd_7137834 3665139674004531425348705 := by
  unfold tailWord_7137834
  simp only [CollatzResearch.WordTrace]
  refine ⟨65084548405713484459795139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173558795748569291892787037 65084548405713484459795139)
  ·
    refine ⟨97626822608570226689692709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65084548405713484459795139 97626822608570226689692709)
    ·
      refine ⟨18305029239106917504317383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97626822608570226689692709 18305029239106917504317383)
      ·
        refine ⟨27457543858660376256476075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18305029239106917504317383 27457543858660376256476075)
        ·
          refine ⟨41186315787990564384714113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27457543858660376256476075 41186315787990564384714113)
          ·
            refine ⟨30889736840992923288535585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41186315787990564384714113 30889736840992923288535585)
            ·
              refine ⟨23167302630744692466401689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30889736840992923288535585 23167302630744692466401689)
              ·
                refine ⟨17375476973058519349801267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23167302630744692466401689 17375476973058519349801267)
                ·
                  refine ⟨26063215459587779024701901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17375476973058519349801267 26063215459587779024701901)
                  ·
                    refine ⟨9773705797345417134263213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26063215459587779024701901 9773705797345417134263213)
                    ·
                      refine ⟨3665139674004531425348705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9773705797345417134263213 3665139674004531425348705)
                      ·
                        rfl

theorem cell23_7137834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_7137834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137834 prefixEnd_7137834 := by exact prefixLift 7137834
  have htrace : WordTrace (prefixWord ++ tailWord_7137834) baseStart_7137834 baseEnd_7137834 := by
    simpa [prefixWord, tailWord_7137834, baseEnd_7137834] using wordTrace_append hprefix tailTrace_7137834
  have hstable : (prefixWord ++ tailWord_7137834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137834).length < 2 ^ (prefixWord ++ tailWord_7137834).sum := by decide
  have hdescent : baseEnd_7137834 < baseStart_7137834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137877 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 2, 4, 3]
def baseStart_7137877 : Nat := 118140960795 + 7137877 * 2 ^ 59
def prefixEnd_7137877 : Nat := 4983230072969 + 3 ^ 40 * 7137877 * 2
def baseEnd_7137877 : Nat := 3665161753672674757111007

theorem tailTrace_7137877 : CollatzResearch.WordTrace tailWord_7137877 prefixEnd_7137877 3665161753672674757111007 := by
  unfold tailWord_7137877
  simp only [CollatzResearch.WordTrace]
  refine ⟨260339761961698156182995885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173559841307798770788663923 260339761961698156182995885)
  ·
    refine ⟨97627410735636808568623457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260339761961698156182995885 97627410735636808568623457)
    ·
      refine ⟨73220558051727606426467593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97627410735636808568623457 73220558051727606426467593)
      ·
        refine ⟨54915418538795704819850695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73220558051727606426467593 54915418538795704819850695)
        ·
          refine ⟨82373127808193557229776043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54915418538795704819850695 82373127808193557229776043)
          ·
            refine ⟨123559691712290335844664065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82373127808193557229776043 123559691712290335844664065)
            ·
              refine ⟨92669768784217751883498049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123559691712290335844664065 92669768784217751883498049)
              ·
                refine ⟨69502326588163313912623537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92669768784217751883498049 69502326588163313912623537)
                ·
                  refine ⟨52126744941122485434467653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69502326588163313912623537 52126744941122485434467653)
                  ·
                    refine ⟨9773764676460466018962685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52126744941122485434467653 9773764676460466018962685)
                    ·
                      refine ⟨3665161753672674757111007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9773764676460466018962685 3665161753672674757111007)
                      ·
                        rfl

theorem cell23_7137877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_7137877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137877 prefixEnd_7137877 := by exact prefixLift 7137877
  have htrace : WordTrace (prefixWord ++ tailWord_7137877) baseStart_7137877 baseEnd_7137877 := by
    simpa [prefixWord, tailWord_7137877, baseEnd_7137877] using wordTrace_append hprefix tailTrace_7137877
  have hstable : (prefixWord ++ tailWord_7137877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137877).length < 2 ^ (prefixWord ++ tailWord_7137877).sum := by decide
  have hdescent : baseEnd_7137877 < baseStart_7137877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137886 : List Nat := [4, 4, 1, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_7137886 : Nat := 118140960795 + 7137886 * 2 ^ 59
def prefixEnd_7137886 : Nat := 4983230072969 + 3 ^ 40 * 7137886 * 2
def baseEnd_7137886 : Nat := 3665166374998565221898467

theorem tailTrace_7137886 : CollatzResearch.WordTrace tailWord_7137886 prefixEnd_7137886 3665166374998565221898467 := by
  unfold tailWord_7137886
  simp only [CollatzResearch.WordTrace]
  refine ⟨32542511277333193840009189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173560060145777033813382341 32542511277333193840009189)
  ·
    refine ⟨6101720864499973845001723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32542511277333193840009189 6101720864499973845001723)
    ·
      refine ⟨9152581296749960767502585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6101720864499973845001723 9152581296749960767502585)
      ·
        refine ⟨6864435972562470575626939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9152581296749960767502585 6864435972562470575626939)
        ·
          refine ⟨10296653958843705863440409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6864435972562470575626939 10296653958843705863440409)
          ·
            refine ⟨7722490469132779397580307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10296653958843705863440409 7722490469132779397580307)
            ·
              refine ⟨11583735703699169096370461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7722490469132779397580307 11583735703699169096370461)
              ·
                refine ⟨4343900888887188411138923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11583735703699169096370461 4343900888887188411138923)
                ·
                  refine ⟨6515851333330782616708385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4343900888887188411138923 6515851333330782616708385)
                  ·
                    refine ⟨4886888499998086962531289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6515851333330782616708385 4886888499998086962531289)
                    ·
                      refine ⟨3665166374998565221898467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4886888499998086962531289 3665166374998565221898467)
                      ·
                        rfl

theorem cell23_7137886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_7137886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137886 prefixEnd_7137886 := by exact prefixLift 7137886
  have htrace : WordTrace (prefixWord ++ tailWord_7137886) baseStart_7137886 baseEnd_7137886 := by
    simpa [prefixWord, tailWord_7137886, baseEnd_7137886] using wordTrace_append hprefix tailTrace_7137886
  have hstable : (prefixWord ++ tailWord_7137886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137886).length < 2 ^ (prefixWord ++ tailWord_7137886).sum := by decide
  have hdescent : baseEnd_7137886 < baseStart_7137886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137907 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 3]
def baseStart_7137907 : Nat := 118140960795 + 7137907 * 2 ^ 59
def prefixEnd_7137907 : Nat := 4983230072969 + 3 ^ 40 * 7137907 * 2
def baseEnd_7137907 : Nat := 3665177158092309639735869

theorem tailTrace_7137907 : CollatzResearch.WordTrace tailWord_7137907 prefixEnd_7137907 3665177158092309639735869 := by
  unfold tailWord_7137907
  simp only [CollatzResearch.WordTrace]
  refine ⟨260340856151589471306587975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173560570767726314204391983 260340856151589471306587975)
  ·
    refine ⟨390511284227384206959881963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260340856151589471306587975 390511284227384206959881963)
    ·
      refine ⟨585766926341076310439822945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390511284227384206959881963 585766926341076310439822945)
      ·
        refine ⟨439325194755807232829867209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585766926341076310439822945 439325194755807232829867209)
        ·
          refine ⟨329493896066855424622400407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439325194755807232829867209 329493896066855424622400407)
          ·
            refine ⟨494240844100283136933600611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329493896066855424622400407 494240844100283136933600611)
            ·
              refine ⟨741361266150424705400400917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494240844100283136933600611 741361266150424705400400917)
              ·
                refine ⟨34751309350801158065643793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 741361266150424705400400917 34751309350801158065643793)
                ·
                  refine ⟨26063482013100868549232845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34751309350801158065643793 26063482013100868549232845)
                  ·
                    refine ⟨9773805754912825705962317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26063482013100868549232845 9773805754912825705962317)
                    ·
                      refine ⟨3665177158092309639735869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9773805754912825705962317 3665177158092309639735869)
                      ·
                        rfl

theorem cell23_7137907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 3].length) (baseStart_7137907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137907 prefixEnd_7137907 := by exact prefixLift 7137907
  have htrace : WordTrace (prefixWord ++ tailWord_7137907) baseStart_7137907 baseEnd_7137907 := by
    simpa [prefixWord, tailWord_7137907, baseEnd_7137907] using wordTrace_append hprefix tailTrace_7137907
  have hstable : (prefixWord ++ tailWord_7137907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137907).length < 2 ^ (prefixWord ++ tailWord_7137907).sum := by decide
  have hdescent : baseEnd_7137907 < baseStart_7137907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137925 : List Nat := [1, 3, 1, 1, 4, 4, 2, 1, 2, 2, 2]
def baseStart_7137925 : Nat := 118140960795 + 7137925 * 2 ^ 59
def prefixEnd_7137925 : Nat := 4983230072969 + 3 ^ 40 * 7137925 * 2
def baseEnd_7137925 : Nat := 3665186400744090569310787

theorem tailTrace_7137925 : CollatzResearch.WordTrace tailWord_7137925 prefixEnd_7137925 3665186400744090569310787 := by
  unfold tailWord_7137925
  simp only [CollatzResearch.WordTrace]
  refine ⟨260341512665524260380743229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173561008443682840253828819 260341512665524260380743229)
  ·
    refine ⟨97628067249571597642778711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260341512665524260380743229 97628067249571597642778711)
    ·
      refine ⟨146442100874357396464168067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97628067249571597642778711 146442100874357396464168067)
      ·
        refine ⟨219663151311536094696252101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146442100874357396464168067 219663151311536094696252101)
        ·
          refine ⟨41186840870913017755547269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219663151311536094696252101 41186840870913017755547269)
          ·
            refine ⟨7722532663296190829165113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41186840870913017755547269 7722532663296190829165113)
            ·
              refine ⟨5791899497472143121873835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7722532663296190829165113 5791899497472143121873835)
              ·
                refine ⟨8687849246208214682810753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5791899497472143121873835 8687849246208214682810753)
                ·
                  refine ⟨6515886934656161012108065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8687849246208214682810753 6515886934656161012108065)
                  ·
                    refine ⟨4886915200992120759081049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6515886934656161012108065 4886915200992120759081049)
                    ·
                      refine ⟨3665186400744090569310787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4886915200992120759081049 3665186400744090569310787)
                      ·
                        rfl

theorem cell23_7137925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 2, 2, 2].length) (baseStart_7137925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137925 prefixEnd_7137925 := by exact prefixLift 7137925
  have htrace : WordTrace (prefixWord ++ tailWord_7137925) baseStart_7137925 baseEnd_7137925 := by
    simpa [prefixWord, tailWord_7137925, baseEnd_7137925] using wordTrace_append hprefix tailTrace_7137925
  have hstable : (prefixWord ++ tailWord_7137925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137925).length < 2 ^ (prefixWord ++ tailWord_7137925).sum := by decide
  have hdescent : baseEnd_7137925 < baseStart_7137925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137927 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 4, 5]
def baseStart_7137927 : Nat := 118140960795 + 7137927 * 2 ^ 59
def prefixEnd_7137927 : Nat := 4983230072969 + 3 ^ 40 * 7137927 * 2
def baseEnd_7137927 : Nat := 1221729142568466520495259

theorem tailTrace_7137927 : CollatzResearch.WordTrace tailWord_7137927 prefixEnd_7137927 1221729142568466520495259 := by
  unfold tailWord_7137927
  simp only [CollatzResearch.WordTrace]
  refine ⟨260341585611517014722316035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173561057074344676481544023 260341585611517014722316035)
  ·
    refine ⟨390512378417275522083474053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260341585611517014722316035 390512378417275522083474053)
    ·
      refine ⟨73221070953239160390651385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 390512378417275522083474053 73221070953239160390651385)
      ·
        refine ⟨54915803214929370292988539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73221070953239160390651385 54915803214929370292988539)
        ·
          refine ⟨82373704822394055439482809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54915803214929370292988539 82373704822394055439482809)
          ·
            refine ⟨61780278616795541579612107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82373704822394055439482809 61780278616795541579612107)
            ·
              refine ⟨92670417925193312369418161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61780278616795541579612107 92670417925193312369418161)
              ·
                refine ⟨69502813443894984277063621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92670417925193312369418161 69502813443894984277063621)
                ·
                  refine ⟨13031777520730309551949429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69502813443894984277063621 13031777520730309551949429)
                  ·
                    refine ⟨1221729142568466520495259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13031777520730309551949429 1221729142568466520495259)
                    ·
                      rfl

theorem cell23_7137927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_7137927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137927 prefixEnd_7137927 := by exact prefixLift 7137927
  have htrace : WordTrace (prefixWord ++ tailWord_7137927) baseStart_7137927 baseEnd_7137927 := by
    simpa [prefixWord, tailWord_7137927, baseEnd_7137927] using wordTrace_append hprefix tailTrace_7137927
  have hstable : (prefixWord ++ tailWord_7137927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137927).length < 2 ^ (prefixWord ++ tailWord_7137927).sum := by decide
  have hdescent : baseEnd_7137927 < baseStart_7137927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137944 : List Nat := [2, 1, 2, 4, 1, 1, 4, 1, 2, 5]
def baseStart_7137944 : Nat := 118140960795 + 7137944 * 2 ^ 59
def prefixEnd_7137944 : Nat := 4983230072969 + 3 ^ 40 * 7137944 * 2
def baseEnd_7137944 : Nat := 1221732052292175331657733

theorem tailTrace_7137944 : CollatzResearch.WordTrace tailWord_7137944 prefixEnd_7137944 1221732052292175331657733 := by
  unfold tailWord_7137944
  simp only [CollatzResearch.WordTrace]
  refine ⟨130171102826227713312842443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173561470434970284417123257 130171102826227713312842443)
  ·
    refine ⟨195256654239341569969263665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130171102826227713312842443 195256654239341569969263665)
    ·
      refine ⟨146442490679506177476947749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195256654239341569969263665 146442490679506177476947749)
      ·
        refine ⟨27457967002407408276927703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146442490679506177476947749 27457967002407408276927703)
        ·
          refine ⟨41186950503611112415391555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27457967002407408276927703 41186950503611112415391555)
          ·
            refine ⟨61780425755416668623087333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41186950503611112415391555 61780425755416668623087333)
            ·
              refine ⟨11583829829140625366828875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61780425755416668623087333 11583829829140625366828875)
              ·
                refine ⟨17375744743710938050243313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11583829829140625366828875 17375744743710938050243313)
                ·
                  refine ⟨13031808557783203537682485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17375744743710938050243313 13031808557783203537682485)
                  ·
                    refine ⟨1221732052292175331657733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13031808557783203537682485 1221732052292175331657733)
                    ·
                      rfl

theorem cell23_7137944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_7137944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137944 prefixEnd_7137944 := by exact prefixLift 7137944
  have htrace : WordTrace (prefixWord ++ tailWord_7137944) baseStart_7137944 baseEnd_7137944 := by
    simpa [prefixWord, tailWord_7137944, baseEnd_7137944] using wordTrace_append hprefix tailTrace_7137944
  have hstable : (prefixWord ++ tailWord_7137944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137944).length < 2 ^ (prefixWord ++ tailWord_7137944).sum := by decide
  have hdescent : baseEnd_7137944 < baseStart_7137944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137977 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 2, 4, 4]
def baseStart_7137977 : Nat := 118140960795 + 7137977 * 2 ^ 59
def prefixEnd_7137977 : Nat := 4983230072969 + 3 ^ 40 * 7137977 * 2
def baseEnd_7137977 : Nat := 3665213101738124365860547

theorem tailTrace_7137977 : CollatzResearch.WordTrace tailWord_7137977 prefixEnd_7137977 3665213101738124365860547 := by
  unfold tailWord_7137977
  simp only [CollatzResearch.WordTrace]
  refine ⟨260343409261335873261636185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173562272840890582174424123 260343409261335873261636185)
  ·
    refine ⟨195257556946001904946227139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260343409261335873261636185 195257556946001904946227139)
    ·
      refine ⟨292886335419002857419340709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195257556946001904946227139 292886335419002857419340709)
      ·
        refine ⟨54916187891063035766126383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292886335419002857419340709 54916187891063035766126383)
        ·
          refine ⟨82374281836594553649189575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54916187891063035766126383 82374281836594553649189575)
          ·
            refine ⟨123561422754891830473784363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82374281836594553649189575 123561422754891830473784363)
            ·
              refine ⟨185342134132337745710676545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123561422754891830473784363 185342134132337745710676545)
              ·
                refine ⟨139006600599253309283007409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185342134132337745710676545 139006600599253309283007409)
                ·
                  refine ⟨104254950449439981962255557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139006600599253309283007409 104254950449439981962255557)
                  ·
                    refine ⟨19547803209269996617922917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104254950449439981962255557 19547803209269996617922917)
                    ·
                      refine ⟨3665213101738124365860547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19547803209269996617922917 3665213101738124365860547)
                      ·
                        rfl

theorem cell23_7137977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_7137977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137977 prefixEnd_7137977 := by exact prefixLift 7137977
  have htrace : WordTrace (prefixWord ++ tailWord_7137977) baseStart_7137977 baseEnd_7137977 := by
    simpa [prefixWord, tailWord_7137977, baseEnd_7137977] using wordTrace_append hprefix tailTrace_7137977
  have hstable : (prefixWord ++ tailWord_7137977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137977).length < 2 ^ (prefixWord ++ tailWord_7137977).sum := by decide
  have hdescent : baseEnd_7137977 < baseStart_7137977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7137981 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 2, 4, 2]
def baseStart_7137981 : Nat := 118140960795 + 7137981 * 2 ^ 59
def prefixEnd_7137981 : Nat := 4983230072969 + 3 ^ 40 * 7137981 * 2
def baseEnd_7137981 : Nat := 3665215155660742350210529

theorem tailTrace_7137981 : CollatzResearch.WordTrace tailWord_7137981 prefixEnd_7137981 3665215155660742350210529 := by
  unfold tailWord_7137981
  simp only [CollatzResearch.WordTrace]
  refine ⟨260343555153321381944781797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173562370102214254629854531 260343555153321381944781797)
  ·
    refine ⟨48814416591247759114646587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260343555153321381944781797 48814416591247759114646587)
    ·
      refine ⟨73221624886871638671969881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48814416591247759114646587 73221624886871638671969881)
      ·
        refine ⟨54916218665153729003977411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73221624886871638671969881 54916218665153729003977411)
        ·
          refine ⟨82374327997730593505966117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54916218665153729003977411 82374327997730593505966117)
          ·
            refine ⟨15445186499574486282368647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82374327997730593505966117 15445186499574486282368647)
            ·
              refine ⟨23167779749361729423552971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15445186499574486282368647 23167779749361729423552971)
              ·
                refine ⟨34751669624042594135329457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23167779749361729423552971 34751669624042594135329457)
                ·
                  refine ⟨26063752218031945601497093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34751669624042594135329457 26063752218031945601497093)
                  ·
                    refine ⟨4886953540880989800280705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26063752218031945601497093 4886953540880989800280705)
                    ·
                      refine ⟨3665215155660742350210529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4886953540880989800280705 3665215155660742350210529)
                      ·
                        rfl

theorem cell23_7137981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_7137981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7137981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7137981 prefixEnd_7137981 := by exact prefixLift 7137981
  have htrace : WordTrace (prefixWord ++ tailWord_7137981) baseStart_7137981 baseEnd_7137981 := by
    simpa [prefixWord, tailWord_7137981, baseEnd_7137981] using wordTrace_append hprefix tailTrace_7137981
  have hstable : (prefixWord ++ tailWord_7137981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7137981).length < 2 ^ (prefixWord ++ tailWord_7137981).sum := by decide
  have hdescent : baseEnd_7137981 < baseStart_7137981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7137981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138008 : List Nat := [2, 1, 2, 2, 3, 3, 2, 3, 1, 4]
def baseStart_7138008 : Nat := 118140960795 + 7138008 * 2 ^ 59
def prefixEnd_7138008 : Nat := 4983230072969 + 3 ^ 40 * 7138008 * 2
def baseEnd_7138008 : Nat := 1221743006546137914857635

theorem tailTrace_7138008 : CollatzResearch.WordTrace tailWord_7138008 prefixEnd_7138008 1221743006546137914857635 := by
  unfold tailWord_7138008
  simp only [CollatzResearch.WordTrace]
  refine ⟨130172269962111782778007339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173563026616149043704009785 130172269962111782778007339)
  ·
    refine ⟨195258404943167674167011009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130172269962111782778007339 195258404943167674167011009)
    ·
      refine ⟨146443803707375755625258257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195258404943167674167011009 146443803707375755625258257)
      ·
        refine ⟨109832852780531816718943693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146443803707375755625258257 109832852780531816718943693)
        ·
          refine ⟨41187319792699431269603885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109832852780531816718943693 41187319792699431269603885)
          ·
            refine ⟨15445244922262286726101457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41187319792699431269603885 15445244922262286726101457)
            ·
              refine ⟨11583933691696715044576093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15445244922262286726101457 11583933691696715044576093)
              ·
                refine ⟨4343975134386268141716035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11583933691696715044576093 4343975134386268141716035)
                ·
                  refine ⟨6515962701579402212574053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4343975134386268141716035 6515962701579402212574053)
                  ·
                    refine ⟨1221743006546137914857635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6515962701579402212574053 1221743006546137914857635)
                    ·
                      rfl

theorem cell23_7138008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 1, 4].length) (baseStart_7138008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138008 prefixEnd_7138008 := by exact prefixLift 7138008
  have htrace : WordTrace (prefixWord ++ tailWord_7138008) baseStart_7138008 baseEnd_7138008 := by
    simpa [prefixWord, tailWord_7138008, baseEnd_7138008] using wordTrace_append hprefix tailTrace_7138008
  have hstable : (prefixWord ++ tailWord_7138008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138008).length < 2 ^ (prefixWord ++ tailWord_7138008).sum := by decide
  have hdescent : baseEnd_7138008 < baseStart_7138008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138021 : List Nat := [1, 3, 1, 4, 1, 4, 1, 2, 6]
def baseStart_7138021 : Nat := 118140960795 + 7138021 * 2 ^ 59
def prefixEnd_7138021 : Nat := 4983230072969 + 3 ^ 40 * 7138021 * 2
def baseEnd_7138021 : Nat := 407248410542991354856705

theorem tailTrace_7138021 : CollatzResearch.WordTrace tailWord_7138021 prefixEnd_7138021 407248410542991354856705 := by
  unfold tailWord_7138021
  simp only [CollatzResearch.WordTrace]
  refine ⟨260345014073176468776237917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173563342715450979184158611 260345014073176468776237917)
  ·
    refine ⟨97629380277441175791089219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260345014073176468776237917 97629380277441175791089219)
    ·
      refine ⟨146444070416161763686633829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97629380277441175791089219 146444070416161763686633829)
      ·
        refine ⟨27458263203030330691243843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146444070416161763686633829 27458263203030330691243843)
        ·
          refine ⟨41187394804545496036865765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27458263203030330691243843 41187394804545496036865765)
          ·
            refine ⟨7722636525852280506912331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41187394804545496036865765 7722636525852280506912331)
            ·
              refine ⟨11583954788778420760368497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7722636525852280506912331 11583954788778420760368497)
              ·
                refine ⟨8687966091583815570276373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11583954788778420760368497 8687966091583815570276373)
                ·
                  refine ⟨407248410542991354856705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8687966091583815570276373 407248410542991354856705)
                  ·
                    rfl

theorem cell23_7138021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 6].length) (baseStart_7138021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138021 prefixEnd_7138021 := by exact prefixLift 7138021
  have htrace : WordTrace (prefixWord ++ tailWord_7138021) baseStart_7138021 baseEnd_7138021 := by
    simpa [prefixWord, tailWord_7138021, baseEnd_7138021] using wordTrace_append hprefix tailTrace_7138021
  have hstable : (prefixWord ++ tailWord_7138021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138021).length < 2 ^ (prefixWord ++ tailWord_7138021).sum := by decide
  have hdescent : baseEnd_7138021 < baseStart_7138021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138031 : List Nat := [1, 1, 2, 1, 5, 2, 1, 3, 3, 1, 3]
def baseStart_7138031 : Nat := 118140960795 + 7138031 * 2 ^ 59
def prefixEnd_7138031 : Nat := 4983230072969 + 3 ^ 40 * 7138031 * 2
def baseEnd_7138031 : Nat := 3665240829693467154585299

theorem tailTrace_7138031 : CollatzResearch.WordTrace tailWord_7138031 prefixEnd_7138031 3665240829693467154585299 := by
  unfold tailWord_7138031
  simp only [CollatzResearch.WordTrace]
  refine ⟨260345378803140240484101947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173563585868760160322734631 260345378803140240484101947)
  ·
    refine ⟨390518068204710360726152921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260345378803140240484101947 390518068204710360726152921)
    ·
      refine ⟨292888551153532770544614691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390518068204710360726152921 292888551153532770544614691)
      ·
        refine ⟨439332826730299155816922037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292888551153532770544614691 439332826730299155816922037)
        ·
          refine ⟨41187452505965545857836441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 439332826730299155816922037 41187452505965545857836441)
          ·
            refine ⟨30890589379474159393377331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41187452505965545857836441 30890589379474159393377331)
            ·
              refine ⟨46335884069211239090065997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30890589379474159393377331 46335884069211239090065997)
              ·
                refine ⟨17375956525954214658774749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46335884069211239090065997 17375956525954214658774749)
                ·
                  refine ⟨6515983697232830497040531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17375956525954214658774749 6515983697232830497040531)
                  ·
                    refine ⟨9773975545849245745560797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6515983697232830497040531 9773975545849245745560797)
                    ·
                      refine ⟨3665240829693467154585299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9773975545849245745560797 3665240829693467154585299)
                      ·
                        rfl

theorem cell23_7138031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 1, 3].length) (baseStart_7138031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138031 prefixEnd_7138031 := by exact prefixLift 7138031
  have htrace : WordTrace (prefixWord ++ tailWord_7138031) baseStart_7138031 baseEnd_7138031 := by
    simpa [prefixWord, tailWord_7138031, baseEnd_7138031] using wordTrace_append hprefix tailTrace_7138031
  have hstable : (prefixWord ++ tailWord_7138031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138031).length < 2 ^ (prefixWord ++ tailWord_7138031).sum := by decide
  have hdescent : baseEnd_7138031 < baseStart_7138031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138081 : List Nat := [1, 2, 3, 2, 1, 2, 2, 4, 2, 4]
def baseStart_7138081 : Nat := 118140960795 + 7138081 * 2 ^ 59
def prefixEnd_7138081 : Nat := 4983230072969 + 3 ^ 40 * 7138081 * 2
def baseEnd_7138081 : Nat := 1221755501242063986320023

theorem tailTrace_7138081 : CollatzResearch.WordTrace tailWord_7138081 prefixEnd_7138081 1221755501242063986320023 := by
  unfold tailWord_7138081
  simp only [CollatzResearch.WordTrace]
  refine ⟨260347202452959099023422097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173564801635306066015614731 260347202452959099023422097)
  ·
    refine ⟨195260401839719324267566573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260347202452959099023422097 195260401839719324267566573)
    ·
      refine ⟨73222650689894746600337465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195260401839719324267566573 73222650689894746600337465)
      ·
        refine ⟨54916988017421059950253099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73222650689894746600337465 54916988017421059950253099)
        ·
          refine ⟨82375482026131589925379649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54916988017421059950253099 82375482026131589925379649)
          ·
            refine ⟨61781611519598692444034737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82375482026131589925379649 61781611519598692444034737)
            ·
              refine ⟨46336208639699019333026053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61781611519598692444034737 46336208639699019333026053)
              ·
                refine ⟨8688039119943566124942385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46336208639699019333026053 8688039119943566124942385)
                ·
                  refine ⟨6516029339957674593706789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8688039119943566124942385 6516029339957674593706789)
                  ·
                    refine ⟨1221755501242063986320023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6516029339957674593706789 1221755501242063986320023)
                    ·
                      rfl

theorem cell23_7138081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_7138081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138081 prefixEnd_7138081 := by exact prefixLift 7138081
  have htrace : WordTrace (prefixWord ++ tailWord_7138081) baseStart_7138081 baseEnd_7138081 := by
    simpa [prefixWord, tailWord_7138081, baseEnd_7138081] using wordTrace_append hprefix tailTrace_7138081
  have hstable : (prefixWord ++ tailWord_7138081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138081).length < 2 ^ (prefixWord ++ tailWord_7138081).sum := by decide
  have hdescent : baseEnd_7138081 < baseStart_7138081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138082 : List Nat := [3, 3, 1, 1, 2, 3, 3, 2, 1, 1, 3]
def baseStart_7138082 : Nat := 118140960795 + 7138082 * 2 ^ 59
def prefixEnd_7138082 : Nat := 4983230072969 + 3 ^ 40 * 7138082 * 2
def baseEnd_7138082 : Nat := 3665267017206846455047565

theorem tailTrace_7138082 : CollatzResearch.WordTrace tailWord_7138082 prefixEnd_7138082 3665267017206846455047565 := by
  unfold tailWord_7138082
  simp only [CollatzResearch.WordTrace]
  refine ⟨65086809731488869048552125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173564825950636984129472333 65086809731488869048552125)
  ·
    refine ⟨24407553649308325893207047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65086809731488869048552125 24407553649308325893207047)
    ·
      refine ⟨36611330473962488839810571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24407553649308325893207047 36611330473962488839810571)
      ·
        refine ⟨54916995710943733259715857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36611330473962488839810571 54916995710943733259715857)
        ·
          refine ⟨41187746783207799944786893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54916995710943733259715857 41187746783207799944786893)
          ·
            refine ⟨15445405043702924979295085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41187746783207799944786893 15445405043702924979295085)
            ·
              refine ⟨5792026891388596867235657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15445405043702924979295085 5792026891388596867235657)
              ·
                refine ⟨4344020168541447650426743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5792026891388596867235657 4344020168541447650426743)
                ·
                  refine ⟨6516030252812171475640115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344020168541447650426743 6516030252812171475640115)
                  ·
                    refine ⟨9774045379218257213460173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6516030252812171475640115 9774045379218257213460173)
                    ·
                      refine ⟨3665267017206846455047565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9774045379218257213460173 3665267017206846455047565)
                      ·
                        rfl

theorem cell23_7138082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_7138082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138082 prefixEnd_7138082 := by exact prefixLift 7138082
  have htrace : WordTrace (prefixWord ++ tailWord_7138082) baseStart_7138082 baseEnd_7138082 := by
    simpa [prefixWord, tailWord_7138082, baseEnd_7138082] using wordTrace_append hprefix tailTrace_7138082
  have hstable : (prefixWord ++ tailWord_7138082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138082).length < 2 ^ (prefixWord ++ tailWord_7138082).sum := by decide
  have hdescent : baseEnd_7138082 < baseStart_7138082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138102 : List Nat := [5, 1, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_7138102 : Nat := 118140960795 + 7138102 * 2 ^ 59
def prefixEnd_7138102 : Nat := 4983230072969 + 3 ^ 40 * 7138102 * 2
def baseEnd_7138102 : Nat := 1221759095606645458932491

theorem tailTrace_7138102 : CollatzResearch.WordTrace tailWord_7138102 prefixEnd_7138102 1221759095606645458932491 := by
  unfold tailWord_7138102
  simp only [CollatzResearch.WordTrace]
  refine ⟨16271748024117688725621035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173565312257255346406624373 16271748024117688725621035)
  ·
    refine ⟨24407622036176533088431553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16271748024117688725621035 24407622036176533088431553)
    ·
      refine ⟨18305716527132399816323665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24407622036176533088431553 18305716527132399816323665)
      ·
        refine ⟨13729287395349299862242749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18305716527132399816323665 13729287395349299862242749)
        ·
          refine ⟨5148482773255987448341031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13729287395349299862242749 5148482773255987448341031)
          ·
            refine ⟨7722724159883981172511547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5148482773255987448341031 7722724159883981172511547)
            ·
              refine ⟨11584086239825971758767321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7722724159883981172511547 11584086239825971758767321)
              ·
                refine ⟨8688064679869478819075491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11584086239825971758767321 8688064679869478819075491)
                ·
                  refine ⟨13032097019804218228613237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8688064679869478819075491 13032097019804218228613237)
                  ·
                    refine ⟨1221759095606645458932491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13032097019804218228613237 1221759095606645458932491)
                    ·
                      rfl

theorem cell23_7138102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_7138102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138102 prefixEnd_7138102 := by exact prefixLift 7138102
  have htrace : WordTrace (prefixWord ++ tailWord_7138102) baseStart_7138102 baseEnd_7138102 := by
    simpa [prefixWord, tailWord_7138102, baseEnd_7138102] using wordTrace_append hprefix tailTrace_7138102
  have hstable : (prefixWord ++ tailWord_7138102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138102).length < 2 ^ (prefixWord ++ tailWord_7138102).sum := by decide
  have hdescent : baseEnd_7138102 < baseStart_7138102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138121 : List Nat := [1, 2, 1, 1, 2, 6, 1, 2, 1, 3, 3]
def baseStart_7138121 : Nat := 118140960795 + 7138121 * 2 ^ 59
def prefixEnd_7138121 : Nat := 4983230072969 + 3 ^ 40 * 7138121 * 2
def baseEnd_7138121 : Nat := 3665287042952371802459885

theorem tailTrace_7138121 : CollatzResearch.WordTrace tailWord_7138121 prefixEnd_7138121 3665287042952371802459885 := by
  unfold tailWord_7138121
  simp only [CollatzResearch.WordTrace]
  refine ⟨260348661372814185854878217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173565774248542790569918811 260348661372814185854878217)
  ·
    refine ⟨195261496029610639391158663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260348661372814185854878217 195261496029610639391158663)
    ·
      refine ⟨292892244044415959086737995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195261496029610639391158663 292892244044415959086737995)
      ·
        refine ⟨439338366066623938630106993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292892244044415959086737995 439338366066623938630106993)
        ·
          refine ⟨329503774549967953972580245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439338366066623938630106993 329503774549967953972580245)
          ·
            refine ⟨15445489432029747842464699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 329503774549967953972580245 15445489432029747842464699)
            ·
              refine ⟨23168234148044621763697049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15445489432029747842464699 23168234148044621763697049)
              ·
                refine ⟨17376175611033466322772787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23168234148044621763697049 17376175611033466322772787)
                ·
                  refine ⟨26064263416550199484159181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17376175611033466322772787 26064263416550199484159181)
                  ·
                    refine ⟨9774098781206324806559693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26064263416550199484159181 9774098781206324806559693)
                    ·
                      refine ⟨3665287042952371802459885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9774098781206324806559693 3665287042952371802459885)
                      ·
                        rfl

theorem cell23_7138121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 3, 3].length) (baseStart_7138121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138121 prefixEnd_7138121 := by exact prefixLift 7138121
  have htrace : WordTrace (prefixWord ++ tailWord_7138121) baseStart_7138121 baseEnd_7138121 := by
    simpa [prefixWord, tailWord_7138121, baseEnd_7138121] using wordTrace_append hprefix tailTrace_7138121
  have hstable : (prefixWord ++ tailWord_7138121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138121).length < 2 ^ (prefixWord ++ tailWord_7138121).sum := by decide
  have hdescent : baseEnd_7138121 < baseStart_7138121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138125 : List Nat := [1, 6, 1, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_7138125 : Nat := 118140960795 + 7138125 * 2 ^ 59
def prefixEnd_7138125 : Nat := 4983230072969 + 3 ^ 40 * 7138125 * 2
def baseEnd_7138125 : Nat := 3665289096874989786809867

theorem tailTrace_7138125 : CollatzResearch.WordTrace tailWord_7138125 prefixEnd_7138125 3665289096874989786809867 := by
  unfold tailWord_7138125
  simp only [CollatzResearch.WordTrace]
  refine ⟨260348807264799694538023829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173565871509866463025349219 260348807264799694538023829)
  ·
    refine ⟨12203850340537485681469867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 260348807264799694538023829 12203850340537485681469867)
    ·
      refine ⟨18305775510806228522204801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12203850340537485681469867 18305775510806228522204801)
      ·
        refine ⟨13729331633104671391653601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18305775510806228522204801 13729331633104671391653601)
        ·
          refine ⟨10296998724828503543740201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13729331633104671391653601 10296998724828503543740201)
          ·
            refine ⟨7722749043621377657805151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10296998724828503543740201 7722749043621377657805151)
            ·
              refine ⟨11584123565432066486707727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7722749043621377657805151 11584123565432066486707727)
              ·
                refine ⟨17376185348148099730061591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11584123565432066486707727 17376185348148099730061591)
                ·
                  refine ⟨26064278022222149595092387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17376185348148099730061591 26064278022222149595092387)
                  ·
                    refine ⟨39096417033333224392638581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26064278022222149595092387 39096417033333224392638581)
                    ·
                      refine ⟨3665289096874989786809867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39096417033333224392638581 3665289096874989786809867)
                      ·
                        rfl

theorem cell23_7138125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_7138125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138125 prefixEnd_7138125 := by exact prefixLift 7138125
  have htrace : WordTrace (prefixWord ++ tailWord_7138125) baseStart_7138125 baseEnd_7138125 := by
    simpa [prefixWord, tailWord_7138125, baseEnd_7138125] using wordTrace_append hprefix tailTrace_7138125
  have hstable : (prefixWord ++ tailWord_7138125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138125).length < 2 ^ (prefixWord ++ tailWord_7138125).sum := by decide
  have hdescent : baseEnd_7138125 < baseStart_7138125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138138 : List Nat := [3, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3]
def baseStart_7138138 : Nat := 118140960795 + 7138138 * 2 ^ 59
def prefixEnd_7138138 : Nat := 4983230072969 + 3 ^ 40 * 7138138 * 2
def baseEnd_7138138 : Nat := 3665295772123498235947307

theorem tailTrace_7138138 : CollatzResearch.WordTrace tailWord_7138138 prefixEnd_7138138 3665295772123498235947307 := by
  unfold tailWord_7138138
  simp only [CollatzResearch.WordTrace]
  refine ⟨65087320353438149439561767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173566187609168398505498045 65087320353438149439561767)
  ·
    refine ⟨97630980530157224159342651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65087320353438149439561767 97630980530157224159342651)
    ·
      refine ⟨146446470795235836239013977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97630980530157224159342651 146446470795235836239013977)
      ·
        refine ⟨109834853096426877179260483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146446470795235836239013977 109834853096426877179260483)
        ·
          refine ⟨164752279644640315768890725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109834853096426877179260483 164752279644640315768890725)
          ·
            refine ⟨30891052433370059206667011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164752279644640315768890725 30891052433370059206667011)
            ·
              refine ⟨46336578650055088810000517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30891052433370059206667011 46336578650055088810000517)
              ·
                refine ⟨8688108496885329151875097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46336578650055088810000517 8688108496885329151875097)
                ·
                  refine ⟨6516081372663996863906323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8688108496885329151875097 6516081372663996863906323)
                  ·
                    refine ⟨9774122058995995295859485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6516081372663996863906323 9774122058995995295859485)
                    ·
                      refine ⟨3665295772123498235947307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9774122058995995295859485 3665295772123498235947307)
                      ·
                        rfl

theorem cell23_7138138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_7138138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138138 prefixEnd_7138138 := by exact prefixLift 7138138
  have htrace : WordTrace (prefixWord ++ tailWord_7138138) baseStart_7138138 baseEnd_7138138 := by
    simpa [prefixWord, tailWord_7138138, baseEnd_7138138] using wordTrace_append hprefix tailTrace_7138138
  have hstable : (prefixWord ++ tailWord_7138138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138138).length < 2 ^ (prefixWord ++ tailWord_7138138).sum := by decide
  have hdescent : baseEnd_7138138 < baseStart_7138138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138144 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 4]
def baseStart_7138144 : Nat := 118140960795 + 7138144 * 2 ^ 59
def prefixEnd_7138144 : Nat := 4983230072969 + 3 ^ 40 * 7138144 * 2
def baseEnd_7138144 : Nat := 3665298853007425212472279

theorem tailTrace_7138144 : CollatzResearch.WordTrace tailWord_7138144 prefixEnd_7138144 3665298853007425212472279 := by
  unfold tailWord_7138144
  simp only [CollatzResearch.WordTrace]
  refine ⟨130174750125865430391482743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173566333501153907188643657 130174750125865430391482743)
  ·
    refine ⟨195262125188798145587224115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130174750125865430391482743 195262125188798145587224115)
    ·
      refine ⟨292893187783197218380836173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195262125188798145587224115 292893187783197218380836173)
      ·
        refine ⟨109834945418698956892813565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292893187783197218380836173 109834945418698956892813565)
        ·
          refine ⟨41188104532012108834805087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109834945418698956892813565 41188104532012108834805087)
          ·
            refine ⟨61782156798018163252207631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41188104532012108834805087 61782156798018163252207631)
            ·
              refine ⟨92673235197027244878311447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61782156798018163252207631 92673235197027244878311447)
              ·
                refine ⟨139009852795540867317467171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92673235197027244878311447 139009852795540867317467171)
                ·
                  refine ⟨208514779193311300976200757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139009852795540867317467171 208514779193311300976200757)
                  ·
                    refine ⟨19548260549372934466518821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 208514779193311300976200757 19548260549372934466518821)
                    ·
                      refine ⟨3665298853007425212472279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19548260549372934466518821 3665298853007425212472279)
                      ·
                        rfl

theorem cell23_7138144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_7138144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138144 prefixEnd_7138144 := by exact prefixLift 7138144
  have htrace : WordTrace (prefixWord ++ tailWord_7138144) baseStart_7138144 baseEnd_7138144 := by
    simpa [prefixWord, tailWord_7138144, baseEnd_7138144] using wordTrace_append hprefix tailTrace_7138144
  have hstable : (prefixWord ++ tailWord_7138144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138144).length < 2 ^ (prefixWord ++ tailWord_7138144).sum := by decide
  have hdescent : baseEnd_7138144 < baseStart_7138144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138148 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 3, 3, 2]
def baseStart_7138148 : Nat := 118140960795 + 7138148 * 2 ^ 59
def prefixEnd_7138148 : Nat := 4983230072969 + 3 ^ 40 * 7138148 * 2
def baseEnd_7138148 : Nat := 3665300906930043196822261

theorem tailTrace_7138148 : CollatzResearch.WordTrace tailWord_7138148 prefixEnd_7138148 3665300906930043196822261 := by
  unfold tailWord_7138148
  simp only [CollatzResearch.WordTrace]
  refine ⟨130174823071858184733055549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173566430762477579644074065 130174823071858184733055549)
  ·
    refine ⟨48815558651946819274895831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130174823071858184733055549 48815558651946819274895831)
    ·
      refine ⟨73223337977920228912343747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48815558651946819274895831 73223337977920228912343747)
      ·
        refine ⟨109835006966880343368515621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73223337977920228912343747 109835006966880343368515621)
        ·
          refine ⟨20594063806290064381596679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109835006966880343368515621 20594063806290064381596679)
          ·
            refine ⟨30891095709435096572395019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20594063806290064381596679 30891095709435096572395019)
            ·
              refine ⟨46336643564152644858592529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30891095709435096572395019 46336643564152644858592529)
              ·
                refine ⟨34752482673114483643944397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46336643564152644858592529 34752482673114483643944397)
                ·
                  refine ⟨13032181002417931366479149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34752482673114483643944397 13032181002417931366479149)
                  ·
                    refine ⟨4887067875906724262429681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13032181002417931366479149 4887067875906724262429681)
                    ·
                      refine ⟨3665300906930043196822261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4887067875906724262429681 3665300906930043196822261)
                      ·
                        rfl

theorem cell23_7138148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_7138148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138148 prefixEnd_7138148 := by exact prefixLift 7138148
  have htrace : WordTrace (prefixWord ++ tailWord_7138148) baseStart_7138148 baseEnd_7138148 := by
    simpa [prefixWord, tailWord_7138148, baseEnd_7138148] using wordTrace_append hprefix tailTrace_7138148
  have hstable : (prefixWord ++ tailWord_7138148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138148).length < 2 ^ (prefixWord ++ tailWord_7138148).sum := by decide
  have hdescent : baseEnd_7138148 < baseStart_7138148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138211 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 3]
def baseStart_7138211 : Nat := 118140960795 + 7138211 * 2 ^ 59
def prefixEnd_7138211 : Nat := 4983230072969 + 3 ^ 40 * 7138211 * 2
def baseEnd_7138211 : Nat := 3665333256211276450334471

theorem tailTrace_7138211 : CollatzResearch.WordTrace tailWord_7138211 prefixEnd_7138211 3665333256211276450334471 := by
  unfold tailWord_7138211
  simp only [CollatzResearch.WordTrace]
  refine ⟨260351943942488131225654487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173567962628325420817102991 260351943942488131225654487)
  ·
    refine ⟨390527915913732196838481731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260351943942488131225654487 390527915913732196838481731)
    ·
      refine ⟨585791873870598295257722597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390527915913732196838481731 585791873870598295257722597)
      ·
        refine ⟨109835976350737180360822987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 585791873870598295257722597 109835976350737180360822987)
        ·
          refine ⟨164753964526105770541234481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109835976350737180360822987 164753964526105770541234481)
          ·
            refine ⟨123565473394579327905925861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164753964526105770541234481 123565473394579327905925861)
            ·
              refine ⟨23168526261483623982361099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123565473394579327905925861 23168526261483623982361099)
              ·
                refine ⟨34752789392225435973541649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23168526261483623982361099 34752789392225435973541649)
                ·
                  refine ⟨26064592044169076980156237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34752789392225435973541649 26064592044169076980156237)
                  ·
                    refine ⟨9774222016563403867558589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26064592044169076980156237 9774222016563403867558589)
                    ·
                      refine ⟨3665333256211276450334471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9774222016563403867558589 3665333256211276450334471)
                      ·
                        rfl

theorem cell23_7138211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_7138211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138211 prefixEnd_7138211 := by exact prefixLift 7138211
  have htrace : WordTrace (prefixWord ++ tailWord_7138211) baseStart_7138211 baseEnd_7138211 := by
    simpa [prefixWord, tailWord_7138211, baseEnd_7138211] using wordTrace_append hprefix tailTrace_7138211
  have hstable : (prefixWord ++ tailWord_7138211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138211).length < 2 ^ (prefixWord ++ tailWord_7138211).sum := by decide
  have hdescent : baseEnd_7138211 < baseStart_7138211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138212 : List Nat := [2, 3, 1, 2, 1, 2, 5, 1, 2, 2, 2]
def baseStart_7138212 : Nat := 118140960795 + 7138212 * 2 ^ 59
def prefixEnd_7138212 : Nat := 4983230072969 + 3 ^ 40 * 7138212 * 2
def baseEnd_7138212 : Nat := 3665333769691930946421967

theorem tailTrace_7138212 : CollatzResearch.WordTrace tailWord_7138212 prefixEnd_7138212 3665333769691930946421967 := by
  unfold tailWord_7138212
  simp only [CollatzResearch.WordTrace]
  refine ⟨130175990207742254198220445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173567986943656338930960593 130175990207742254198220445)
  ·
    refine ⟨48815996327903345324332667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130175990207742254198220445 48815996327903345324332667)
    ·
      refine ⟨73223994491855017986499001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48815996327903345324332667 73223994491855017986499001)
      ·
        refine ⟨54917995868891263489874251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73223994491855017986499001 54917995868891263489874251)
        ·
          refine ⟨82376993803336895234811377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54917995868891263489874251 82376993803336895234811377)
          ·
            refine ⟨61782745352502671426108533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82376993803336895234811377 61782745352502671426108533)
            ·
              refine ⟨5792132376797125446197675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61782745352502671426108533 5792132376797125446197675)
              ·
                refine ⟨8688198565195688169296513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5792132376797125446197675 8688198565195688169296513)
                ·
                  refine ⟨6516148923896766126972385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8688198565195688169296513 6516148923896766126972385)
                  ·
                    refine ⟨4887111692922574595229289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6516148923896766126972385 4887111692922574595229289)
                    ·
                      refine ⟨3665333769691930946421967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4887111692922574595229289 3665333769691930946421967)
                      ·
                        rfl

theorem cell23_7138212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_7138212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138212 prefixEnd_7138212 := by exact prefixLift 7138212
  have htrace : WordTrace (prefixWord ++ tailWord_7138212) baseStart_7138212 baseEnd_7138212 := by
    simpa [prefixWord, tailWord_7138212, baseEnd_7138212] using wordTrace_append hprefix tailTrace_7138212
  have hstable : (prefixWord ++ tailWord_7138212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138212).length < 2 ^ (prefixWord ++ tailWord_7138212).sum := by decide
  have hdescent : baseEnd_7138212 < baseStart_7138212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138248 : List Nat := [2, 1, 3, 1, 5, 1, 1, 2, 2, 5]
def baseStart_7138248 : Nat := 118140960795 + 7138248 * 2 ^ 59
def prefixEnd_7138248 : Nat := 4983230072969 + 3 ^ 40 * 7138248 * 2
def baseEnd_7138248 : Nat := 1221784084998497601857267

theorem tailTrace_7138248 : CollatzResearch.WordTrace tailWord_7138248 prefixEnd_7138248 1221784084998497601857267 := by
  unfold tailWord_7138248
  simp only [CollatzResearch.WordTrace]
  refine ⟨130176646721677043272375699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173568862295569391029834265 130176646721677043272375699)
  ·
    refine ⟨195264970082515564908563549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130176646721677043272375699 195264970082515564908563549)
    ·
      refine ⟨73224363780943336840711331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195264970082515564908563549 73224363780943336840711331)
      ·
        refine ⟨109836545671415005261066997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73224363780943336840711331 109836545671415005261066997)
        ·
          refine ⟨10297176156695156743225031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109836545671415005261066997 10297176156695156743225031)
          ·
            refine ⟨15445764235042735114837547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10297176156695156743225031 15445764235042735114837547)
            ·
              refine ⟨23168646352564102672256321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15445764235042735114837547 23168646352564102672256321)
              ·
                refine ⟨17376484764423077004192241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23168646352564102672256321 17376484764423077004192241)
                ·
                  refine ⟨13032363573317307753144181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17376484764423077004192241 13032363573317307753144181)
                  ·
                    refine ⟨1221784084998497601857267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13032363573317307753144181 1221784084998497601857267)
                    ·
                      rfl

theorem cell23_7138248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_7138248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138248 prefixEnd_7138248 := by exact prefixLift 7138248
  have htrace : WordTrace (prefixWord ++ tailWord_7138248) baseStart_7138248 baseEnd_7138248 := by
    simpa [prefixWord, tailWord_7138248, baseEnd_7138248] using wordTrace_append hprefix tailTrace_7138248
  have hstable : (prefixWord ++ tailWord_7138248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138248).length < 2 ^ (prefixWord ++ tailWord_7138248).sum := by decide
  have hdescent : baseEnd_7138248 < baseStart_7138248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138251 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 4]
def baseStart_7138251 : Nat := 118140960795 + 7138251 * 2 ^ 59
def prefixEnd_7138251 : Nat := 4983230072969 + 3 ^ 40 * 7138251 * 2
def baseEnd_7138251 : Nat := 3665353795437456293834287

theorem tailTrace_7138251 : CollatzResearch.WordTrace tailWord_7138251 prefixEnd_7138251 3665353795437456293834287 := by
  unfold tailWord_7138251
  simp only [CollatzResearch.WordTrace]
  refine ⟨260353402862343218057110607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173568935241562145371407071 260353402862343218057110607)
  ·
    refine ⟨390530104293514827085665911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260353402862343218057110607 390530104293514827085665911)
    ·
      refine ⟨585795156440272240628498867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390530104293514827085665911 585795156440272240628498867)
      ·
        refine ⟨878692734660408360942748301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585795156440272240628498867 878692734660408360942748301)
        ·
          refine ⟨329509775497653135353530613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 878692734660408360942748301 329509775497653135353530613)
          ·
            refine ⟨30891541452904981439393495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 329509775497653135353530613 30891541452904981439393495)
            ·
              refine ⟨46337312179357472159090243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30891541452904981439393495 46337312179357472159090243)
              ·
                refine ⟨69505968269036208238635365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46337312179357472159090243 69505968269036208238635365)
                ·
                  refine ⟨13032369050444289044744131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69505968269036208238635365 13032369050444289044744131)
                  ·
                    refine ⟨19548553575666433567116197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13032369050444289044744131 19548553575666433567116197)
                    ·
                      refine ⟨3665353795437456293834287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19548553575666433567116197 3665353795437456293834287)
                      ·
                        rfl

theorem cell23_7138251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 4].length) (baseStart_7138251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138251 prefixEnd_7138251 := by exact prefixLift 7138251
  have htrace : WordTrace (prefixWord ++ tailWord_7138251) baseStart_7138251 baseEnd_7138251 := by
    simpa [prefixWord, tailWord_7138251, baseEnd_7138251] using wordTrace_append hprefix tailTrace_7138251
  have hstable : (prefixWord ++ tailWord_7138251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138251).length < 2 ^ (prefixWord ++ tailWord_7138251).sum := by decide
  have hdescent : baseEnd_7138251 < baseStart_7138251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138258 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_7138258 : Nat := 118140960795 + 7138258 * 2 ^ 59
def prefixEnd_7138258 : Nat := 4983230072969 + 3 ^ 40 * 7138258 * 2
def baseEnd_7138258 : Nat := 3665357389802037766446755

theorem tailTrace_7138258 : CollatzResearch.WordTrace tailWord_7138258 prefixEnd_7138258 3665357389802037766446755 := by
  unfold tailWord_7138258
  simp only [CollatzResearch.WordTrace]
  refine ⟨65088414543329464563153857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173569105448878572168410285 65088414543329464563153857)
  ·
    refine ⟨48816310907497098422365393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65088414543329464563153857 48816310907497098422365393)
    ·
      refine ⟨36612233180622823816774045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48816310907497098422365393 36612233180622823816774045)
      ·
        refine ⟨13729587442733558931290267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36612233180622823816774045 13729587442733558931290267)
        ·
          refine ⟨20594381164100338396935401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13729587442733558931290267 20594381164100338396935401)
          ·
            refine ⟨15445785873075253797701551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20594381164100338396935401 15445785873075253797701551)
            ·
              refine ⟨23168678809612880696552327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15445785873075253797701551 23168678809612880696552327)
              ·
                refine ⟨34753018214419321044828491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23168678809612880696552327 34753018214419321044828491)
                ·
                  refine ⟨52129527321628981567242737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34753018214419321044828491 52129527321628981567242737)
                  ·
                    refine ⟨39097145491221736175432053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52129527321628981567242737 39097145491221736175432053)
                    ·
                      refine ⟨3665357389802037766446755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39097145491221736175432053 3665357389802037766446755)
                      ·
                        rfl

theorem cell23_7138258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_7138258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138258 prefixEnd_7138258 := by exact prefixLift 7138258
  have htrace : WordTrace (prefixWord ++ tailWord_7138258) baseStart_7138258 baseEnd_7138258 := by
    simpa [prefixWord, tailWord_7138258, baseEnd_7138258] using wordTrace_append hprefix tailTrace_7138258
  have hstable : (prefixWord ++ tailWord_7138258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138258).length < 2 ^ (prefixWord ++ tailWord_7138258).sum := by decide
  have hdescent : baseEnd_7138258 < baseStart_7138258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138311 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_7138311 : Nat := 118140960795 + 7138311 * 2 ^ 59
def prefixEnd_7138311 : Nat := 4983230072969 + 3 ^ 40 * 7138311 * 2
def baseEnd_7138311 : Nat := 3665384604276726059084011

theorem tailTrace_7138311 : CollatzResearch.WordTrace tailWord_7138311 prefixEnd_7138311 3665384604276726059084011 := by
  unfold tailWord_7138311
  simp only [CollatzResearch.WordTrace]
  refine ⟨260355591242125848304294787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173570394161417232202863191 260355591242125848304294787)
  ·
    refine ⟨390533386863188772456442181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260355591242125848304294787 390533386863188772456442181)
    ·
      refine ⟨73225010036847894835582909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 390533386863188772456442181 73225010036847894835582909)
      ·
        refine ⟨27459378763817960563343591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73225010036847894835582909 27459378763817960563343591)
        ·
          refine ⟨41189068145726940845015387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27459378763817960563343591 41189068145726940845015387)
          ·
            refine ⟨61783602218590411267523081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41189068145726940845015387 61783602218590411267523081)
            ·
              refine ⟨46337701663942808450642311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61783602218590411267523081 46337701663942808450642311)
              ·
                refine ⟨69506552495914212675963467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46337701663942808450642311 69506552495914212675963467)
                ·
                  refine ⟨104259828743871319013945201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69506552495914212675963467 104259828743871319013945201)
                  ·
                    refine ⟨78194871557903489260458901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104259828743871319013945201 78194871557903489260458901)
                    ·
                      refine ⟨3665384604276726059084011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78194871557903489260458901 3665384604276726059084011)
                      ·
                        rfl

theorem cell23_7138311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_7138311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138311 prefixEnd_7138311 := by exact prefixLift 7138311
  have htrace : WordTrace (prefixWord ++ tailWord_7138311) baseStart_7138311 baseEnd_7138311 := by
    simpa [prefixWord, tailWord_7138311, baseEnd_7138311] using wordTrace_append hprefix tailTrace_7138311
  have hstable : (prefixWord ++ tailWord_7138311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138311).length < 2 ^ (prefixWord ++ tailWord_7138311).sum := by decide
  have hdescent : baseEnd_7138311 < baseStart_7138311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138312 : List Nat := [2, 1, 3, 2, 1, 3, 4, 2, 1, 4]
def baseStart_7138312 : Nat := 118140960795 + 7138312 * 2 ^ 59
def prefixEnd_7138312 : Nat := 4983230072969 + 3 ^ 40 * 7138312 * 2
def baseEnd_7138312 : Nat := 1221795039252460185057169

theorem tailTrace_7138312 : CollatzResearch.WordTrace tailWord_7138312 prefixEnd_7138312 1221795039252460185057169 := by
  unfold tailWord_7138312
  simp only [CollatzResearch.WordTrace]
  refine ⟨130177813857561112737540595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173570418476748150316720793 130177813857561112737540595)
  ·
    refine ⟨195266720786341669106310893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130177813857561112737540595 195266720786341669106310893)
    ·
      refine ⟨73225020294878125914866585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195266720786341669106310893 73225020294878125914866585)
      ·
        refine ⟨54918765221158594436149939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73225020294878125914866585 54918765221158594436149939)
        ·
          refine ⟨82378147831737891654224909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54918765221158594436149939 82378147831737891654224909)
          ·
            refine ⟨30891805436901709370334341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82378147831737891654224909 30891805436901709370334341)
            ·
              refine ⟨5792213519419070506937689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30891805436901709370334341 5792213519419070506937689)
              ·
                refine ⟨4344160139564302880203267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5792213519419070506937689 4344160139564302880203267)
                ·
                  refine ⟨6516240209346454320304901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344160139564302880203267 6516240209346454320304901)
                  ·
                    refine ⟨1221795039252460185057169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6516240209346454320304901 1221795039252460185057169)
                    ·
                      rfl

theorem cell23_7138312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_7138312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138312 prefixEnd_7138312 := by exact prefixLift 7138312
  have htrace : WordTrace (prefixWord ++ tailWord_7138312) baseStart_7138312 baseEnd_7138312 := by
    simpa [prefixWord, tailWord_7138312, baseEnd_7138312] using wordTrace_append hprefix tailTrace_7138312
  have hstable : (prefixWord ++ tailWord_7138312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138312).length < 2 ^ (prefixWord ++ tailWord_7138312).sum := by decide
  have hdescent : baseEnd_7138312 < baseStart_7138312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7138335 : List Nat := [1, 1, 2, 4, 1, 4, 1, 2, 3, 1, 3]
def baseStart_7138335 : Nat := 118140960795 + 7138335 * 2 ^ 59
def prefixEnd_7138335 : Nat := 4983230072969 + 3 ^ 40 * 7138335 * 2
def baseEnd_7138335 : Nat := 3665396927812433965183901

theorem tailTrace_7138335 : CollatzResearch.WordTrace tailWord_7138335 prefixEnd_7138335 3665396927812433965183901 := by
  unfold tailWord_7138335
  simp only [CollatzResearch.WordTrace]
  refine ⟨260356466594038900403168459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173570977729359266935445639 260356466594038900403168459)
  ·
    refine ⟨390534699891058350604752689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260356466594038900403168459 390534699891058350604752689)
    ·
      refine ⟨292901024918293762953564517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390534699891058350604752689 292901024918293762953564517)
      ·
        refine ⟨54918942172180080553793347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292901024918293762953564517 54918942172180080553793347)
        ·
          refine ⟨82378413258270120830690021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54918942172180080553793347 82378413258270120830690021)
          ·
            refine ⟨15445952485925647655754379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82378413258270120830690021 15445952485925647655754379)
            ·
              refine ⟨23168928728888471483631569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15445952485925647655754379 23168928728888471483631569)
              ·
                refine ⟨17376696546666353612723677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23168928728888471483631569 17376696546666353612723677)
                ·
                  refine ⟨6516261204999882604771379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17376696546666353612723677 6516261204999882604771379)
                  ·
                    refine ⟨9774391807499823907157069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6516261204999882604771379 9774391807499823907157069)
                    ·
                      refine ⟨3665396927812433965183901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9774391807499823907157069 3665396927812433965183901)
                      ·
                        rfl

theorem cell23_7138335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_7138335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7138335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7138335 prefixEnd_7138335 := by exact prefixLift 7138335
  have htrace : WordTrace (prefixWord ++ tailWord_7138335) baseStart_7138335 baseEnd_7138335 := by
    simpa [prefixWord, tailWord_7138335, baseEnd_7138335] using wordTrace_append hprefix tailTrace_7138335
  have hstable : (prefixWord ++ tailWord_7138335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7138335).length < 2 ^ (prefixWord ++ tailWord_7138335).sum := by decide
  have hdescent : baseEnd_7138335 < baseStart_7138335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7138335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
