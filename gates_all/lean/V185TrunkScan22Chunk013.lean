import V185TrunkScan22Chunk012

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_113626 : List Nat := [3, 1, 1, 2, 4, 1, 3, 2, 5]
def baseStart_113626 : Nat := 118140960795 + 113626 * 2 ^ 59
def prefixEnd_113626 : Nat := 4983230072969 + 3 ^ 40 * 113626 * 2
def baseEnd_113626 : Nat := 12965500632861704767211

theorem tailTrace_113626 : CollatzResearch.WordTrace tailWord_113626 prefixEnd_113626 12965500632861704767211 := by
  unfold tailWord_113626
  simp only [CollatzResearch.WordTrace]
  refine ⟨1036070171589970655234183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2762853790906588413957821 1036070171589970655234183)
  ·
    refine ⟨1554105257384955982851275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1036070171589970655234183 1554105257384955982851275)
    ·
      refine ⟨2331157886077433974276913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1554105257384955982851275 2331157886077433974276913)
      ·
        refine ⟨1748368414558075480707685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2331157886077433974276913 1748368414558075480707685)
        ·
          refine ⟨327819077729639152632691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1748368414558075480707685 327819077729639152632691)
          ·
            refine ⟨491728616594458728949037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327819077729639152632691 491728616594458728949037)
            ·
              refine ⟨184398231222922023355889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 491728616594458728949037 184398231222922023355889)
              ·
                refine ⟨138298673417191517516917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184398231222922023355889 138298673417191517516917)
                ·
                  refine ⟨12965500632861704767211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138298673417191517516917 12965500632861704767211)
                  ·
                    rfl

theorem cell22_113626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_113626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113626 prefixEnd_113626 := by exact prefixLift 113626
  have htrace : WordTrace (prefixWord ++ tailWord_113626) baseStart_113626 baseEnd_113626 := by
    simpa [prefixWord, tailWord_113626, baseEnd_113626] using wordTrace_append hprefix tailTrace_113626
  have hstable : (prefixWord ++ tailWord_113626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113626).length < 2 ^ (prefixWord ++ tailWord_113626).sum := by decide
  have hdescent : baseEnd_113626 < baseStart_113626 := by decide
  rcases family_descends (prefixWord ++ tailWord_113626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113669 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 3, 5]
def baseStart_113669 : Nat := 118140960795 + 113669 * 2 ^ 59
def prefixEnd_113669 : Nat := 4983230072969 + 3 ^ 40 * 113669 * 2
def baseEnd_113669 : Nat := 38911221677347335476501

theorem tailTrace_113669 : CollatzResearch.WordTrace tailWord_113669 prefixEnd_113669 38911221677347335476501 := by
  unfold tailWord_113669
  simp only [CollatzResearch.WordTrace]
  refine ⟨4145849025204100964752061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2763899350136067309834707 4145849025204100964752061)
  ·
    refine ⟨1554693384451537861782023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4145849025204100964752061 1554693384451537861782023)
    ·
      refine ⟨2332040076677306792673035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1554693384451537861782023 2332040076677306792673035)
      ·
        refine ⟨3498060115015960189009553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2332040076677306792673035 3498060115015960189009553)
        ·
          refine ⟨2623545086261970141757165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3498060115015960189009553 2623545086261970141757165)
          ·
            refine ⟨983829407348238803158937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2623545086261970141757165 983829407348238803158937)
            ·
              refine ⟨737872055511179102369203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 983829407348238803158937 737872055511179102369203)
              ·
                refine ⟨1106808083266768653553805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737872055511179102369203 1106808083266768653553805)
                ·
                  refine ⟨415053031225038245082677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106808083266768653553805 415053031225038245082677)
                  ·
                    refine ⟨38911221677347335476501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 415053031225038245082677 38911221677347335476501)
                    ·
                      rfl

theorem cell22_113669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_113669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113669 prefixEnd_113669 := by exact prefixLift 113669
  have htrace : WordTrace (prefixWord ++ tailWord_113669) baseStart_113669 baseEnd_113669 := by
    simpa [prefixWord, tailWord_113669, baseEnd_113669] using wordTrace_append hprefix tailTrace_113669
  have hstable : (prefixWord ++ tailWord_113669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113669).length < 2 ^ (prefixWord ++ tailWord_113669).sum := by decide
  have hdescent : baseEnd_113669 < baseStart_113669 := by decide
  rcases family_descends (prefixWord ++ tailWord_113669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113699 : List Nat := [1, 1, 1, 4, 3, 2, 1, 9]
def baseStart_113699 : Nat := 118140960795 + 113699 * 2 ^ 59
def prefixEnd_113699 : Nat := 4983230072969 + 3 ^ 40 * 113699 * 2
def baseEnd_113699 : Nat := 4324610143381917469601

theorem tailTrace_113699 : CollatzResearch.WordTrace tailWord_113699 prefixEnd_113699 4324610143381917469601 := by
  unfold tailWord_113699
  simp only [CollatzResearch.WordTrace]
  refine ⟨4146943215095416088344151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2764628810063610725562767 4146943215095416088344151)
  ·
    refine ⟨6220414822643124132516227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4146943215095416088344151 6220414822643124132516227)
    ·
      refine ⟨9330622233964686198774341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6220414822643124132516227 9330622233964686198774341)
      ·
        refine ⟨1749491668868378662270189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9330622233964686198774341 1749491668868378662270189)
        ·
          refine ⟨656059375825641998351321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1749491668868378662270189 656059375825641998351321)
          ·
            refine ⟨492044531869231498763491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 656059375825641998351321 492044531869231498763491)
            ·
              refine ⟨738066797803847248145237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492044531869231498763491 738066797803847248145237)
              ·
                refine ⟨4324610143381917469601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 738066797803847248145237 4324610143381917469601)
                ·
                  rfl

theorem cell22_113699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 9].length) (baseStart_113699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113699 prefixEnd_113699 := by exact prefixLift 113699
  have htrace : WordTrace (prefixWord ++ tailWord_113699) baseStart_113699 baseEnd_113699 := by
    simpa [prefixWord, tailWord_113699, baseEnd_113699] using wordTrace_append hprefix tailTrace_113699
  have hstable : (prefixWord ++ tailWord_113699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113699).length < 2 ^ (prefixWord ++ tailWord_113699).sum := by decide
  have hdescent : baseEnd_113699 < baseStart_113699 := by decide
  rcases family_descends (prefixWord ++ tailWord_113699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113718 : List Nat := [5, 1, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_113718 : Nat := 118140960795 + 113718 * 2 ^ 59
def prefixEnd_113718 : Nat := 4983230072969 + 3 ^ 40 * 113718 * 2
def baseEnd_113718 : Nat := 38927995378727541001351

theorem tailTrace_113718 : CollatzResearch.WordTrace tailWord_113718 prefixEnd_113718 38927995378727541001351 := by
  unfold tailWord_113718
  simp only [CollatzResearch.WordTrace]
  refine ⟨259227262626661395830363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2765090801351054888857205 259227262626661395830363)
  ·
    refine ⟨388840893939992093745545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259227262626661395830363 388840893939992093745545)
    ·
      refine ⟨291630670454994070309159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388840893939992093745545 291630670454994070309159)
      ·
        refine ⟨437446005682491105463739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291630670454994070309159 437446005682491105463739)
        ·
          refine ⟨656169008523736658195609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437446005682491105463739 656169008523736658195609)
          ·
            refine ⟨492126756392802493646707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 656169008523736658195609 492126756392802493646707)
            ·
              refine ⟨738190134589203740470061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492126756392802493646707 738190134589203740470061)
              ·
                refine ⟨276821300470951402676273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 738190134589203740470061 276821300470951402676273)
                ·
                  refine ⟨207615975353213552007205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276821300470951402676273 207615975353213552007205)
                  ·
                    refine ⟨38927995378727541001351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 207615975353213552007205 38927995378727541001351)
                    ·
                      rfl

theorem cell22_113718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_113718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113718 prefixEnd_113718 := by exact prefixLift 113718
  have htrace : WordTrace (prefixWord ++ tailWord_113718) baseStart_113718 baseEnd_113718 := by
    simpa [prefixWord, tailWord_113718, baseEnd_113718] using wordTrace_append hprefix tailTrace_113718
  have hstable : (prefixWord ++ tailWord_113718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113718).length < 2 ^ (prefixWord ++ tailWord_113718).sum := by decide
  have hdescent : baseEnd_113718 < baseStart_113718 := by decide
  rcases family_descends (prefixWord ++ tailWord_113718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113744 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 7]
def baseStart_113744 : Nat := 118140960795 + 113744 * 2 ^ 59
def prefixEnd_113744 : Nat := 4983230072969 + 3 ^ 40 * 113744 * 2
def baseEnd_113744 : Nat := 12978965236690713283757

theorem tailTrace_113744 : CollatzResearch.WordTrace tailWord_113744 prefixEnd_113744 12978965236690713283757 := by
  unfold tailWord_113744
  simp only [CollatzResearch.WordTrace]
  refine ⟨2074292249966194386866143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2765722999954925849154857 2074292249966194386866143)
  ·
    refine ⟨3111438374949291580299215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2074292249966194386866143 3111438374949291580299215)
    ·
      refine ⟨4667157562423937370448823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3111438374949291580299215 4667157562423937370448823)
      ·
        refine ⟨7000736343635906055673235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4667157562423937370448823 7000736343635906055673235)
        ·
          refine ⟨10501104515453859083509853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7000736343635906055673235 10501104515453859083509853)
          ·
            refine ⟨3937914193295197156316195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10501104515453859083509853 3937914193295197156316195)
            ·
              refine ⟨5906871289942795734474293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3937914193295197156316195 5906871289942795734474293)
              ·
                refine ⟨553769183432137100106965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5906871289942795734474293 553769183432137100106965)
                ·
                  refine ⟨12978965236690713283757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 553769183432137100106965 12978965236690713283757)
                  ·
                    rfl

theorem cell22_113744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 7].length) (baseStart_113744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113744 prefixEnd_113744 := by exact prefixLift 113744
  have htrace : WordTrace (prefixWord ++ tailWord_113744) baseStart_113744 baseEnd_113744 := by
    simpa [prefixWord, tailWord_113744, baseEnd_113744] using wordTrace_append hprefix tailTrace_113744
  have hstable : (prefixWord ++ tailWord_113744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113744).length < 2 ^ (prefixWord ++ tailWord_113744).sum := by decide
  have hdescent : baseEnd_113744 < baseStart_113744 := by decide
  rcases family_descends (prefixWord ++ tailWord_113744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113746 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_113746 : Nat := 118140960795 + 113746 * 2 ^ 59
def prefixEnd_113746 : Nat := 4983230072969 + 3 ^ 40 * 113746 * 2
def baseEnd_113746 : Nat := 38937580350944801301265

theorem tailTrace_113746 : CollatzResearch.WordTrace tailWord_113746 prefixEnd_113746 38937580350944801301265 := by
  unfold tailWord_113746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1037164361481285778826273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2765771630616762076870061 1037164361481285778826273)
  ·
    refine ⟨777873271110964334119705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1037164361481285778826273 777873271110964334119705)
    ·
      refine ⟨583404953333223250589779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 777873271110964334119705 583404953333223250589779)
      ·
        refine ⟨875107429999834875884669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583404953333223250589779 875107429999834875884669)
        ·
          refine ⟨328165286249938078456751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 875107429999834875884669 328165286249938078456751)
          ·
            refine ⟨492247929374907117685127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328165286249938078456751 492247929374907117685127)
            ·
              refine ⟨738371894062360676527691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492247929374907117685127 738371894062360676527691)
              ·
                refine ⟨1107557841093541014791537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738371894062360676527691 1107557841093541014791537)
                ·
                  refine ⟨830668380820155761093653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1107557841093541014791537 830668380820155761093653)
                  ·
                    refine ⟨38937580350944801301265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 830668380820155761093653 38937580350944801301265)
                    ·
                      rfl

theorem cell22_113746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_113746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113746 prefixEnd_113746 := by exact prefixLift 113746
  have htrace : WordTrace (prefixWord ++ tailWord_113746) baseStart_113746 baseEnd_113746 := by
    simpa [prefixWord, tailWord_113746, baseEnd_113746] using wordTrace_append hprefix tailTrace_113746
  have hstable : (prefixWord ++ tailWord_113746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113746).length < 2 ^ (prefixWord ++ tailWord_113746).sum := by decide
  have hdescent : baseEnd_113746 < baseStart_113746 := by decide
  rcases family_descends (prefixWord ++ tailWord_113746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113761 : List Nat := [1, 2, 3, 1, 1, 2, 4, 3, 5]
def baseStart_113761 : Nat := 118140960795 + 113761 * 2 ^ 59
def prefixEnd_113761 : Nat := 4983230072969 + 3 ^ 40 * 113761 * 2
def baseEnd_113761 : Nat := 12980905052496587392073

theorem tailTrace_113761 : CollatzResearch.WordTrace tailWord_113761 prefixEnd_113761 12980905052496587392073 := by
  unfold tailWord_113761
  simp only [CollatzResearch.WordTrace]
  refine ⟨4149204540870800677101137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2766136360580533784734091 4149204540870800677101137)
  ·
    refine ⟨3111903405653100507825853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4149204540870800677101137 3111903405653100507825853)
    ·
      refine ⟨1166963777119912690434695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3111903405653100507825853 1166963777119912690434695)
      ·
        refine ⟨1750445665679869035652043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1166963777119912690434695 1750445665679869035652043)
        ·
          refine ⟨2625668498519803553478065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750445665679869035652043 2625668498519803553478065)
          ·
            refine ⟨1969251373889852665108549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2625668498519803553478065 1969251373889852665108549)
            ·
              refine ⟨369234632604347374707853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1969251373889852665108549 369234632604347374707853)
              ·
                refine ⟨138462987226630265515445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369234632604347374707853 138462987226630265515445)
                ·
                  refine ⟨12980905052496587392073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138462987226630265515445 12980905052496587392073)
                  ·
                    rfl

theorem cell22_113761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 5].length) (baseStart_113761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113761 prefixEnd_113761 := by exact prefixLift 113761
  have htrace : WordTrace (prefixWord ++ tailWord_113761) baseStart_113761 baseEnd_113761 := by
    simpa [prefixWord, tailWord_113761, baseEnd_113761] using wordTrace_append hprefix tailTrace_113761
  have hstable : (prefixWord ++ tailWord_113761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113761).length < 2 ^ (prefixWord ++ tailWord_113761).sum := by decide
  have hdescent : baseEnd_113761 < baseStart_113761 := by decide
  rcases family_descends (prefixWord ++ tailWord_113761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113782 : List Nat := [5, 1, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_113782 : Nat := 118140960795 + 113782 * 2 ^ 59
def prefixEnd_113782 : Nat := 4983230072969 + 3 ^ 40 * 113782 * 2
def baseEnd_113782 : Nat := 38949903886652707401155

theorem tailTrace_113782 : CollatzResearch.WordTrace tailWord_113782 prefixEnd_113782 38949903886652707401155 := by
  unfold tailWord_113782
  simp only [CollatzResearch.WordTrace]
  refine ⟨259373154612170078975975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2766646982529814175743733 259373154612170078975975)
  ·
    refine ⟨389059731918255118463963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259373154612170078975975 389059731918255118463963)
    ·
      refine ⟨583589597877382677695945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389059731918255118463963 583589597877382677695945)
      ·
        refine ⟨437692198408037008271959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583589597877382677695945 437692198408037008271959)
        ·
          refine ⟨656538297612055512407939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437692198408037008271959 656538297612055512407939)
          ·
            refine ⟨984807446418083268611909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656538297612055512407939 984807446418083268611909)
            ·
              refine ⟨184651396203390612864733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 984807446418083268611909 184651396203390612864733)
              ·
                refine ⟨69244273576271479824275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184651396203390612864733 69244273576271479824275)
                ·
                  refine ⟨103866410364407219736413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69244273576271479824275 103866410364407219736413)
                  ·
                    refine ⟨38949903886652707401155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103866410364407219736413 38949903886652707401155)
                    ·
                      rfl

theorem cell22_113782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_113782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113782 prefixEnd_113782 := by exact prefixLift 113782
  have htrace : WordTrace (prefixWord ++ tailWord_113782) baseStart_113782 baseEnd_113782 := by
    simpa [prefixWord, tailWord_113782, baseEnd_113782] using wordTrace_append hprefix tailTrace_113782
  have hstable : (prefixWord ++ tailWord_113782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113782).length < 2 ^ (prefixWord ++ tailWord_113782).sum := by decide
  have hdescent : baseEnd_113782 < baseStart_113782 := by decide
  rcases family_descends (prefixWord ++ tailWord_113782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113908 : List Nat := [2, 6, 1, 2, 1, 2, 2, 2, 4]
def baseStart_113908 : Nat := 118140960795 + 113908 * 2 ^ 59
def prefixEnd_113908 : Nat := 4983230072969 + 3 ^ 40 * 113908 * 2
def baseEnd_113908 : Nat := 12997678753876792916923

theorem tailTrace_113908 : CollatzResearch.WordTrace tailWord_113908 prefixEnd_113908 12997678753876792916923 := by
  unfold tailWord_113908
  simp only [CollatzResearch.WordTrace]
  refine ⟨2077283035669122391351189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2769710714225496521801585 2077283035669122391351189)
  ·
    refine ⟨97372642296990112094587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2077283035669122391351189 97372642296990112094587)
    ·
      refine ⟨146058963445485168141881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97372642296990112094587 146058963445485168141881)
      ·
        refine ⟨109544222584113876106411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146058963445485168141881 109544222584113876106411)
        ·
          refine ⟨164316333876170814159617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109544222584113876106411 164316333876170814159617)
          ·
            refine ⟨123237250407128110619713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164316333876170814159617 123237250407128110619713)
            ·
              refine ⟨92427937805346082964785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123237250407128110619713 92427937805346082964785)
              ·
                refine ⟨69320953354009562223589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92427937805346082964785 69320953354009562223589)
                ·
                  refine ⟨12997678753876792916923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69320953354009562223589 12997678753876792916923)
                  ·
                    rfl

theorem cell22_113908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_113908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113908 prefixEnd_113908 := by exact prefixLift 113908
  have htrace : WordTrace (prefixWord ++ tailWord_113908) baseStart_113908 baseEnd_113908 := by
    simpa [prefixWord, tailWord_113908, baseEnd_113908] using wordTrace_append hprefix tailTrace_113908
  have hstable : (prefixWord ++ tailWord_113908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113908).length < 2 ^ (prefixWord ++ tailWord_113908).sum := by decide
  have hdescent : baseEnd_113908 < baseStart_113908 := by decide
  rcases family_descends (prefixWord ++ tailWord_113908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113911 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 4, 5]
def baseStart_113911 : Nat := 118140960795 + 113911 * 2 ^ 59
def prefixEnd_113911 : Nat := 4983230072969 + 3 ^ 40 * 113911 * 2
def baseEnd_113911 : Nat := 38994063222939370925759

theorem tailTrace_113911 : CollatzResearch.WordTrace tailWord_113911 prefixEnd_113911 38994063222939370925759 := by
  unfold tailWord_113911
  simp only [CollatzResearch.WordTrace]
  refine ⟨4154675490327376295061587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2769783660218250863374391 4154675490327376295061587)
  ·
    refine ⟨6232013235491064442592381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4154675490327376295061587 6232013235491064442592381)
    ·
      refine ⟨2337004963309149165972143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6232013235491064442592381 2337004963309149165972143)
      ·
        refine ⟨3505507444963723748958215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2337004963309149165972143 3505507444963723748958215)
        ·
          refine ⟨5258261167445585623437323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3505507444963723748958215 5258261167445585623437323)
          ·
            refine ⟨7887391751168378435155985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5258261167445585623437323 7887391751168378435155985)
            ·
              refine ⟨5915543813376283826366989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7887391751168378435155985 5915543813376283826366989)
              ·
                refine ⟨2218328930016106434887621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5915543813376283826366989 2218328930016106434887621)
                ·
                  refine ⟨415936674378019956541429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2218328930016106434887621 415936674378019956541429)
                  ·
                    refine ⟨38994063222939370925759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 415936674378019956541429 38994063222939370925759)
                    ·
                      rfl

theorem cell22_113911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_113911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113911 prefixEnd_113911 := by exact prefixLift 113911
  have htrace : WordTrace (prefixWord ++ tailWord_113911) baseStart_113911 baseEnd_113911 := by
    simpa [prefixWord, tailWord_113911, baseEnd_113911] using wordTrace_append hprefix tailTrace_113911
  have hstable : (prefixWord ++ tailWord_113911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113911).length < 2 ^ (prefixWord ++ tailWord_113911).sum := by decide
  have hdescent : baseEnd_113911 < baseStart_113911 := by decide
  rcases family_descends (prefixWord ++ tailWord_113911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113913 : List Nat := [1, 2, 1, 3, 1, 1, 6, 2, 5]
def baseStart_113913 : Nat := 118140960795 + 113913 * 2 ^ 59
def prefixEnd_113913 : Nat := 4983230072969 + 3 ^ 40 * 113913 * 2
def baseEnd_113913 : Nat := 12998249287937344125251

theorem tailTrace_113913 : CollatzResearch.WordTrace tailWord_113913 prefixEnd_113913 12998249287937344125251 := by
  unfold tailWord_113913
  simp only [CollatzResearch.WordTrace]
  refine ⟨4154748436320130636634393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2769832290880087091089595 4154748436320130636634393)
  ·
    refine ⟨3116061327240097977475795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4154748436320130636634393 3116061327240097977475795)
    ·
      refine ⟨4674091990860146966213693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3116061327240097977475795 4674091990860146966213693)
      ·
        refine ⟨1752784496572555112330135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4674091990860146966213693 1752784496572555112330135)
        ·
          refine ⟨2629176744858832668495203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1752784496572555112330135 2629176744858832668495203)
          ·
            refine ⟨3943765117288249002742805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629176744858832668495203 3943765117288249002742805)
            ·
              refine ⟨184863989872886672003569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3943765117288249002742805 184863989872886672003569)
              ·
                refine ⟨138647992404665004002677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184863989872886672003569 138647992404665004002677)
                ·
                  refine ⟨12998249287937344125251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138647992404665004002677 12998249287937344125251)
                  ·
                    rfl

theorem cell22_113913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 5].length) (baseStart_113913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113913 prefixEnd_113913 := by exact prefixLift 113913
  have htrace : WordTrace (prefixWord ++ tailWord_113913) baseStart_113913 baseEnd_113913 := by
    simpa [prefixWord, tailWord_113913, baseEnd_113913] using wordTrace_append hprefix tailTrace_113913
  have hstable : (prefixWord ++ tailWord_113913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113913).length < 2 ^ (prefixWord ++ tailWord_113913).sum := by decide
  have hdescent : baseEnd_113913 < baseStart_113913 := by decide
  rcases family_descends (prefixWord ++ tailWord_113913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113943 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 3, 4]
def baseStart_113943 : Nat := 118140960795 + 113943 * 2 ^ 59
def prefixEnd_113943 : Nat := 4983230072969 + 3 ^ 40 * 113943 * 2
def baseEnd_113943 : Nat := 39005017476901954125661

theorem tailTrace_113943 : CollatzResearch.WordTrace tailWord_113943 prefixEnd_113943 39005017476901954125661 := by
  unfold tailWord_113943
  simp only [CollatzResearch.WordTrace]
  refine ⟨4155842626211445760226483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2770561750807630506817655 4155842626211445760226483)
  ·
    refine ⟨6233763939317168640339725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4155842626211445760226483 6233763939317168640339725)
    ·
      refine ⟨2337661477243938240127397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6233763939317168640339725 2337661477243938240127397)
      ·
        refine ⟨438311526983238420023887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2337661477243938240127397 438311526983238420023887)
        ·
          refine ⟨657467290474857630035831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438311526983238420023887 657467290474857630035831)
          ·
            refine ⟨986200935712286445053747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657467290474857630035831 986200935712286445053747)
            ·
              refine ⟨1479301403568429667580621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986200935712286445053747 1479301403568429667580621)
              ·
                refine ⟨554738026338161125342733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1479301403568429667580621 554738026338161125342733)
                ·
                  refine ⟨208026759876810422003525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554738026338161125342733 208026759876810422003525)
                  ·
                    refine ⟨39005017476901954125661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 208026759876810422003525 39005017476901954125661)
                    ·
                      rfl

theorem cell22_113943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_113943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113943 prefixEnd_113943 := by exact prefixLift 113943
  have htrace : WordTrace (prefixWord ++ tailWord_113943) baseStart_113943 baseEnd_113943 := by
    simpa [prefixWord, tailWord_113943, baseEnd_113943] using wordTrace_append hprefix tailTrace_113943
  have hstable : (prefixWord ++ tailWord_113943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113943).length < 2 ^ (prefixWord ++ tailWord_113943).sum := by decide
  have hdescent : baseEnd_113943 < baseStart_113943 := by decide
  rcases family_descends (prefixWord ++ tailWord_113943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114082 : List Nat := [3, 3, 1, 2, 1, 3, 2, 2, 5]
def baseStart_114082 : Nat := 118140960795 + 114082 * 2 ^ 59
def prefixEnd_114082 : Nat := 4983230072969 + 3 ^ 40 * 114082 * 2
def baseEnd_114082 : Nat := 13017533339183974966745

theorem tailTrace_114082 : CollatzResearch.WordTrace tailWord_114082 prefixEnd_114082 13017533339183974966745 := by
  unfold tailWord_114082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1040228093176968124884125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2773941581805248333024333 1040228093176968124884125)
  ·
    refine ⟨390085534941363046831547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1040228093176968124884125 390085534941363046831547)
    ·
      refine ⟨585128302412044570247321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390085534941363046831547 585128302412044570247321)
      ·
        refine ⟨438846226809033427685491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585128302412044570247321 438846226809033427685491)
        ·
          refine ⟨658269340213550141528237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438846226809033427685491 658269340213550141528237)
          ·
            refine ⟨246851002580081303073089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 658269340213550141528237 246851002580081303073089)
            ·
              refine ⟨185138251935060977304817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246851002580081303073089 185138251935060977304817)
              ·
                refine ⟨138853688951295732978613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185138251935060977304817 138853688951295732978613)
                ·
                  refine ⟨13017533339183974966745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138853688951295732978613 13017533339183974966745)
                  ·
                    rfl

theorem cell22_114082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_114082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114082 prefixEnd_114082 := by exact prefixLift 114082
  have htrace : WordTrace (prefixWord ++ tailWord_114082) baseStart_114082 baseEnd_114082 := by
    simpa [prefixWord, tailWord_114082, baseEnd_114082] using wordTrace_append hprefix tailTrace_114082
  have hstable : (prefixWord ++ tailWord_114082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114082).length < 2 ^ (prefixWord ++ tailWord_114082).sum := by decide
  have hdescent : baseEnd_114082 < baseStart_114082 := by decide
  rcases family_descends (prefixWord ++ tailWord_114082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114277 : List Nat := [1, 3, 1, 3, 3, 1, 1, 3, 1, 5]
def baseStart_114277 : Nat := 118140960795 + 114277 * 2 ^ 59
def prefixEnd_114277 : Nat := 4983230072969 + 3 ^ 40 * 114277 * 2
def baseEnd_114277 : Nat := 39119352502636416274637

theorem tailTrace_114277 : CollatzResearch.WordTrace tailWord_114277 prefixEnd_114277 39119352502636416274637 := by
  unfold tailWord_114277
  simp only [CollatzResearch.WordTrace]
  refine ⟨4168024607001420802885085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2778683071334280535256723 4168024607001420802885085)
  ·
    refine ⟨1563009227625532801081907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4168024607001420802885085 1563009227625532801081907)
    ·
      refine ⟨2344513841438299201622861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1563009227625532801081907 2344513841438299201622861)
      ·
        refine ⟨879192690539362200608573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2344513841438299201622861 879192690539362200608573)
        ·
          refine ⟨329697258952260825228215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 879192690539362200608573 329697258952260825228215)
          ·
            refine ⟨494545888428391237842323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329697258952260825228215 494545888428391237842323)
            ·
              refine ⟨741818832642586856763485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494545888428391237842323 741818832642586856763485)
              ·
                refine ⟨278182062240970071286307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 741818832642586856763485 278182062240970071286307)
                ·
                  refine ⟨417273093361455106929461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278182062240970071286307 417273093361455106929461)
                  ·
                    refine ⟨39119352502636416274637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 417273093361455106929461 39119352502636416274637)
                    ·
                      rfl

theorem cell22_114277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_114277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114277 prefixEnd_114277 := by exact prefixLift 114277
  have htrace : WordTrace (prefixWord ++ tailWord_114277) baseStart_114277 baseEnd_114277 := by
    simpa [prefixWord, tailWord_114277, baseEnd_114277] using wordTrace_append hprefix tailTrace_114277
  have hstable : (prefixWord ++ tailWord_114277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114277).length < 2 ^ (prefixWord ++ tailWord_114277).sum := by decide
  have hdescent : baseEnd_114277 < baseStart_114277 := by decide
  rcases family_descends (prefixWord ++ tailWord_114277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114294 : List Nat := [5, 1, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_114294 : Nat := 118140960795 + 114294 * 2 ^ 59
def prefixEnd_114294 : Nat := 4983230072969 + 3 ^ 40 * 114294 * 2
def baseEnd_114294 : Nat := 39125171950054038599585

theorem tailTrace_114294 : CollatzResearch.WordTrace tailWord_114294 prefixEnd_114294 39125171950054038599585 := by
  unfold tailWord_114294
  simp only [CollatzResearch.WordTrace]
  refine ⟨260540290496239544140871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2779096431959888470835957 260540290496239544140871)
  ·
    refine ⟨390810435744359316211307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260540290496239544140871 390810435744359316211307)
    ·
      refine ⟨586215653616538974316961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390810435744359316211307 586215653616538974316961)
      ·
        refine ⟨439661740212404230737721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 586215653616538974316961 439661740212404230737721)
        ·
          refine ⟨329746305159303173053291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439661740212404230737721 329746305159303173053291)
          ·
            refine ⟨494619457738954759579937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329746305159303173053291 494619457738954759579937)
            ·
              refine ⟨370964593304216069684953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494619457738954759579937 370964593304216069684953)
              ·
                refine ⟨278223444978162052263715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370964593304216069684953 278223444978162052263715)
                ·
                  refine ⟨417335167467243078395573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278223444978162052263715 417335167467243078395573)
                  ·
                    refine ⟨39125171950054038599585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 417335167467243078395573 39125171950054038599585)
                    ·
                      rfl

theorem cell22_114294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_114294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114294 prefixEnd_114294 := by exact prefixLift 114294
  have htrace : WordTrace (prefixWord ++ tailWord_114294) baseStart_114294 baseEnd_114294 := by
    simpa [prefixWord, tailWord_114294, baseEnd_114294] using wordTrace_append hprefix tailTrace_114294
  have hstable : (prefixWord ++ tailWord_114294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114294).length < 2 ^ (prefixWord ++ tailWord_114294).sum := by decide
  have hdescent : baseEnd_114294 < baseStart_114294 := by decide
  rcases family_descends (prefixWord ++ tailWord_114294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114311 : List Nat := [1, 1, 4, 2, 1, 5, 1, 2, 2, 3]
def baseStart_114311 : Nat := 118140960795 + 114311 * 2 ^ 59
def prefixEnd_114311 : Nat := 4983230072969 + 3 ^ 40 * 114311 * 2
def baseEnd_114311 : Nat := 39130991397471660924533

theorem tailTrace_114311 : CollatzResearch.WordTrace tailWord_114311 prefixEnd_114311 39130991397471660924533 := by
  unfold tailWord_114311
  simp only [CollatzResearch.WordTrace]
  refine ⟨4169264688878244609622787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2779509792585496406415191 4169264688878244609622787)
  ·
    refine ⟨6253897033317366914434181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4169264688878244609622787 6253897033317366914434181)
    ·
      refine ⟨1172605693747006296456409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6253897033317366914434181 1172605693747006296456409)
      ·
        refine ⟨879454270310254722342307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1172605693747006296456409 879454270310254722342307)
        ·
          refine ⟨1319181405465382083513461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879454270310254722342307 1319181405465382083513461)
          ·
            refine ⟨123673256762379570329387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1319181405465382083513461 123673256762379570329387)
            ·
              refine ⟨185509885143569355494081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123673256762379570329387 185509885143569355494081)
              ·
                refine ⟨139132413857677016620561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185509885143569355494081 139132413857677016620561)
                ·
                  refine ⟨104349310393257762465421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139132413857677016620561 104349310393257762465421)
                  ·
                    refine ⟨39130991397471660924533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104349310393257762465421 39130991397471660924533)
                    ·
                      rfl

theorem cell22_114311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_114311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114311 prefixEnd_114311 := by exact prefixLift 114311
  have htrace : WordTrace (prefixWord ++ tailWord_114311) baseStart_114311 baseEnd_114311 := by
    simpa [prefixWord, tailWord_114311, baseEnd_114311] using wordTrace_append hprefix tailTrace_114311
  have hstable : (prefixWord ++ tailWord_114311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114311).length < 2 ^ (prefixWord ++ tailWord_114311).sum := by decide
  have hdescent : baseEnd_114311 < baseStart_114311 := by decide
  rcases family_descends (prefixWord ++ tailWord_114311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114320 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 1, 8]
def baseStart_114320 : Nat := 118140960795 + 114320 * 2 ^ 59
def prefixEnd_114320 : Nat := 4983230072969 + 3 ^ 40 * 114320 * 2
def baseEnd_114320 : Nat := 39134072281398637449505

theorem tailTrace_114320 : CollatzResearch.WordTrace tailWord_114320 prefixEnd_114320 39134072281398637449505 := by
  unfold tailWord_114320
  simp only [CollatzResearch.WordTrace]
  refine ⟨2084796472922819573350207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2779728630563759431133609 2084796472922819573350207)
  ·
    refine ⟨3127194709384229360025311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2084796472922819573350207 3127194709384229360025311)
    ·
      refine ⟨4690792064076344040037967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3127194709384229360025311 4690792064076344040037967)
      ·
        refine ⟨7036188096114516060056951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4690792064076344040037967 7036188096114516060056951)
        ·
          refine ⟨10554282144171774090085427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7036188096114516060056951 10554282144171774090085427)
          ·
            refine ⟨15831423216257661135128141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10554282144171774090085427 15831423216257661135128141)
            ·
              refine ⟨5936783706096622925673053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15831423216257661135128141 5936783706096622925673053)
              ·
                refine ⟨2226293889786233597127395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5936783706096622925673053 2226293889786233597127395)
                ·
                  refine ⟨3339440834679350395691093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226293889786233597127395 3339440834679350395691093)
                  ·
                    refine ⟨39134072281398637449505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3339440834679350395691093 39134072281398637449505)
                    ·
                      rfl

theorem cell22_114320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_114320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114320 prefixEnd_114320 := by exact prefixLift 114320
  have htrace : WordTrace (prefixWord ++ tailWord_114320) baseStart_114320 baseEnd_114320 := by
    simpa [prefixWord, tailWord_114320, baseEnd_114320] using wordTrace_append hprefix tailTrace_114320
  have hstable : (prefixWord ++ tailWord_114320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114320).length < 2 ^ (prefixWord ++ tailWord_114320).sum := by decide
  have hdescent : baseEnd_114320 < baseStart_114320 := by decide
  rcases family_descends (prefixWord ++ tailWord_114320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114386 : List Nat := [3, 2, 2, 2, 2, 1, 4, 1, 5]
def baseStart_114386 : Nat := 118140960795 + 114386 * 2 ^ 59
def prefixEnd_114386 : Nat := 4983230072969 + 3 ^ 40 * 114386 * 2
def baseEnd_114386 : Nat := 13052221810065488433101

theorem tailTrace_114386 : CollatzResearch.WordTrace tailWord_114386 prefixEnd_114386 13052221810065488433101 := by
  unfold tailWord_114386
  simp only [CollatzResearch.WordTrace]
  refine ⟨1043000040901633104650753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2781333442404354945735341 1043000040901633104650753)
  ·
    refine ⟨782250030676224828488065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1043000040901633104650753 782250030676224828488065)
    ·
      refine ⟨586687523007168621366049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 782250030676224828488065 586687523007168621366049)
      ·
        refine ⟨440015642255376466024537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 586687523007168621366049 440015642255376466024537)
        ·
          refine ⟨330011731691532349518403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440015642255376466024537 330011731691532349518403)
          ·
            refine ⟨495017597537298524277605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330011731691532349518403 495017597537298524277605)
            ·
              refine ⟨92815799538243473302051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 495017597537298524277605 92815799538243473302051)
              ·
                refine ⟨139223699307365209953077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92815799538243473302051 139223699307365209953077)
                ·
                  refine ⟨13052221810065488433101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139223699307365209953077 13052221810065488433101)
                  ·
                    rfl

theorem cell22_114386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_114386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114386 prefixEnd_114386 := by exact prefixLift 114386
  have htrace : WordTrace (prefixWord ++ tailWord_114386) baseStart_114386 baseEnd_114386 := by
    simpa [prefixWord, tailWord_114386, baseEnd_114386] using wordTrace_append hprefix tailTrace_114386
  have hstable : (prefixWord ++ tailWord_114386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114386).length < 2 ^ (prefixWord ++ tailWord_114386).sum := by decide
  have hdescent : baseEnd_114386 < baseStart_114386 := by decide
  rcases family_descends (prefixWord ++ tailWord_114386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114412 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 3, 5]
def baseStart_114412 : Nat := 118140960795 + 114412 * 2 ^ 59
def prefixEnd_114412 : Nat := 4983230072969 + 3 ^ 40 * 114412 * 2
def baseEnd_114412 : Nat := 39165565761541064149223

theorem tailTrace_114412 : CollatzResearch.WordTrace tailWord_114412 prefixEnd_114412 39165565761541064149223 := by
  unfold tailWord_114412
  simp only [CollatzResearch.WordTrace]
  refine ⟨2086474230756169429524745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2781965641008225906032993 2086474230756169429524745)
  ·
    refine ⟨1564855673067127072143559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2086474230756169429524745 1564855673067127072143559)
    ·
      refine ⟨2347283509600690608215339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1564855673067127072143559 2347283509600690608215339)
      ·
        refine ⟨3520925264401035912323009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2347283509600690608215339 3520925264401035912323009)
        ·
          refine ⟨2640693948300776934242257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3520925264401035912323009 2640693948300776934242257)
          ·
            refine ⟨1980520461225582700681693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2640693948300776934242257 1980520461225582700681693)
            ·
              refine ⟨742695172959593512755635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1980520461225582700681693 742695172959593512755635)
              ·
                refine ⟨1114042759439390269133453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742695172959593512755635 1114042759439390269133453)
                ·
                  refine ⟨417766034789771350925045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114042759439390269133453 417766034789771350925045)
                  ·
                    refine ⟨39165565761541064149223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 417766034789771350925045 39165565761541064149223)
                    ·
                      rfl

theorem cell22_114412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_114412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114412 prefixEnd_114412 := by exact prefixLift 114412
  have htrace : WordTrace (prefixWord ++ tailWord_114412) baseStart_114412 baseEnd_114412 := by
    simpa [prefixWord, tailWord_114412, baseEnd_114412] using wordTrace_append hprefix tailTrace_114412
  have hstable : (prefixWord ++ tailWord_114412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114412).length < 2 ^ (prefixWord ++ tailWord_114412).sum := by decide
  have hdescent : baseEnd_114412 < baseStart_114412 := by decide
  rcases family_descends (prefixWord ++ tailWord_114412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114427 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 4, 4]
def baseStart_114427 : Nat := 118140960795 + 114427 * 2 ^ 59
def prefixEnd_114427 : Nat := 4983230072969 + 3 ^ 40 * 114427 * 2
def baseEnd_114427 : Nat := 39170700568086025024177

theorem tailTrace_114427 : CollatzResearch.WordTrace tailWord_114427 prefixEnd_114427 39170700568086025024177 := by
  unfold tailWord_114427
  simp only [CollatzResearch.WordTrace]
  refine ⟨4173495556457996420845535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2782330370971997613897023 4173495556457996420845535)
  ·
    refine ⟨6260243334686994631268303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4173495556457996420845535 6260243334686994631268303)
    ·
      refine ⟨9390365002030491946902455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6260243334686994631268303 9390365002030491946902455)
      ·
        refine ⟨14085547503045737920353683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9390365002030491946902455 14085547503045737920353683)
        ·
          refine ⟨21128321254568606880530525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14085547503045737920353683 21128321254568606880530525)
          ·
            refine ⟨7923120470463227580198947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21128321254568606880530525 7923120470463227580198947)
            ·
              refine ⟨11884680705694841370298421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7923120470463227580198947 11884680705694841370298421)
              ·
                refine ⟨1114188816158891378465477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11884680705694841370298421 1114188816158891378465477)
                ·
                  refine ⟨208910403029792133462277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1114188816158891378465477 208910403029792133462277)
                  ·
                    refine ⟨39170700568086025024177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 208910403029792133462277 39170700568086025024177)
                    ·
                      rfl

theorem cell22_114427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 4].length) (baseStart_114427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114427 prefixEnd_114427 := by exact prefixLift 114427
  have htrace : WordTrace (prefixWord ++ tailWord_114427) baseStart_114427 baseEnd_114427 := by
    simpa [prefixWord, tailWord_114427, baseEnd_114427] using wordTrace_append hprefix tailTrace_114427
  have hstable : (prefixWord ++ tailWord_114427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114427).length < 2 ^ (prefixWord ++ tailWord_114427).sum := by decide
  have hdescent : baseEnd_114427 < baseStart_114427 := by decide
  rcases family_descends (prefixWord ++ tailWord_114427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114431 : List Nat := [1, 1, 2, 2, 1, 3, 6, 2, 4]
def baseStart_114431 : Nat := 118140960795 + 114431 * 2 ^ 59
def prefixEnd_114431 : Nat := 4983230072969 + 3 ^ 40 * 114431 * 2
def baseEnd_114431 : Nat := 13057356616610449308055

theorem tailTrace_114431 : CollatzResearch.WordTrace tailWord_114431 prefixEnd_114431 13057356616610449308055 := by
  unfold tailWord_114431
  simp only [CollatzResearch.WordTrace]
  refine ⟨4173641448443505103991147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2782427632295670069327431 4173641448443505103991147)
  ·
    refine ⟨6260462172665257655986721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4173641448443505103991147 6260462172665257655986721)
    ·
      refine ⟨4695346629498943241990041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6260462172665257655986721 4695346629498943241990041)
      ·
        refine ⟨3521509972124207431492531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4695346629498943241990041 3521509972124207431492531)
        ·
          refine ⟨5282264958186311147238797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3521509972124207431492531 5282264958186311147238797)
          ·
            refine ⟨1980849359319866680214549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5282264958186311147238797 1980849359319866680214549)
            ·
              refine ⟨92852313718118750635057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1980849359319866680214549 92852313718118750635057)
              ·
                refine ⟨69639235288589062976293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92852313718118750635057 69639235288589062976293)
                ·
                  refine ⟨13057356616610449308055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69639235288589062976293 13057356616610449308055)
                  ·
                    rfl

theorem cell22_114431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 4].length) (baseStart_114431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114431 prefixEnd_114431 := by exact prefixLift 114431
  have htrace : WordTrace (prefixWord ++ tailWord_114431) baseStart_114431 baseEnd_114431 := by
    simpa [prefixWord, tailWord_114431, baseEnd_114431] using wordTrace_append hprefix tailTrace_114431
  have hstable : (prefixWord ++ tailWord_114431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114431).length < 2 ^ (prefixWord ++ tailWord_114431).sum := by decide
  have hdescent : baseEnd_114431 < baseStart_114431 := by decide
  rcases family_descends (prefixWord ++ tailWord_114431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114446 : List Nat := [4, 1, 1, 2, 1, 1, 4, 3, 2, 3]
def baseStart_114446 : Nat := 118140960795 + 114446 * 2 ^ 59
def prefixEnd_114446 : Nat := 4983230072969 + 3 ^ 40 * 114446 * 2
def baseEnd_114446 : Nat := 39177204656376308799119

theorem tailTrace_114446 : CollatzResearch.WordTrace tailWord_114446 prefixEnd_114446 39177204656376308799119 := by
  unfold tailWord_114446
  simp only [CollatzResearch.WordTrace]
  refine ⟨521773567923645333223399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2782792362259441777191461 521773567923645333223399)
  ·
    refine ⟨782660351885467999835099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 521773567923645333223399 782660351885467999835099)
    ·
      refine ⟨1173990527828201999752649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 782660351885467999835099 1173990527828201999752649)
      ·
        refine ⟨880492895871151499814487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1173990527828201999752649 880492895871151499814487)
        ·
          refine ⟨1320739343806727249721731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880492895871151499814487 1320739343806727249721731)
          ·
            refine ⟨1981109015710090874582597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320739343806727249721731 1981109015710090874582597)
            ·
              refine ⟨371457940445642038984237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1981109015710090874582597 371457940445642038984237)
              ·
                refine ⟨139296727667115764619089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 371457940445642038984237 139296727667115764619089)
                ·
                  refine ⟨104472545750336823464317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139296727667115764619089 104472545750336823464317)
                  ·
                    refine ⟨39177204656376308799119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104472545750336823464317 39177204656376308799119)
                    ·
                      rfl

theorem cell22_114446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_114446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114446 prefixEnd_114446 := by exact prefixLift 114446
  have htrace : WordTrace (prefixWord ++ tailWord_114446) baseStart_114446 baseEnd_114446 := by
    simpa [prefixWord, tailWord_114446, baseEnd_114446] using wordTrace_append hprefix tailTrace_114446
  have hstable : (prefixWord ++ tailWord_114446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114446).length < 2 ^ (prefixWord ++ tailWord_114446).sum := by decide
  have hdescent : baseEnd_114446 < baseStart_114446 := by decide
  rcases family_descends (prefixWord ++ tailWord_114446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114542 : List Nat := [4, 1, 2, 3, 1, 2, 3, 2, 1, 3]
def baseStart_114542 : Nat := 118140960795 + 114542 * 2 ^ 59
def prefixEnd_114542 : Nat := 4983230072969 + 3 ^ 40 * 114542 * 2
def baseEnd_114542 : Nat := 39210067418264058398825

theorem tailTrace_114542 : CollatzResearch.WordTrace tailWord_114542 prefixEnd_114542 39210067418264058398825 := by
  unfold tailWord_114542
  simp only [CollatzResearch.WordTrace]
  refine ⟨522211243880171382660235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2785126634027580707521253 522211243880171382660235)
  ·
    refine ⟨783316865820257073990353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 522211243880171382660235 783316865820257073990353)
    ·
      refine ⟨587487649365192805492765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 783316865820257073990353 587487649365192805492765)
      ·
        refine ⟨220307868511947302059787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 587487649365192805492765 220307868511947302059787)
        ·
          refine ⟨330461802767920953089681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220307868511947302059787 330461802767920953089681)
          ·
            refine ⟨247846352075940714817261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330461802767920953089681 247846352075940714817261)
            ·
              refine ⟨92942382028477768056473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247846352075940714817261 92942382028477768056473)
              ·
                refine ⟨69706786521358326042355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92942382028477768056473 69706786521358326042355)
                ·
                  refine ⟨104560179782037489063533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69706786521358326042355 104560179782037489063533)
                  ·
                    refine ⟨39210067418264058398825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104560179782037489063533 39210067418264058398825)
                    ·
                      rfl

theorem cell22_114542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_114542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114542 prefixEnd_114542 := by exact prefixLift 114542
  have htrace : WordTrace (prefixWord ++ tailWord_114542) baseStart_114542 baseEnd_114542 := by
    simpa [prefixWord, tailWord_114542, baseEnd_114542] using wordTrace_append hprefix tailTrace_114542
  have hstable : (prefixWord ++ tailWord_114542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114542).length < 2 ^ (prefixWord ++ tailWord_114542).sum := by decide
  have hdescent : baseEnd_114542 < baseStart_114542 := by decide
  rcases family_descends (prefixWord ++ tailWord_114542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114594 : List Nat := [3, 3, 1, 2, 13]
def baseStart_114594 : Nat := 118140960795 + 114594 * 2 ^ 59
def prefixEnd_114594 : Nat := 4983230072969 + 3 ^ 40 * 114594 * 2
def baseEnd_114594 : Nat := 161431555888696527155

theorem tailTrace_114594 : CollatzResearch.WordTrace tailWord_114594 prefixEnd_114594 161431555888696527155 := by
  unfold tailWord_114594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1044896636713245985543709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2786391031235322628116557 1044896636713245985543709)
  ·
    refine ⟨391836238767467244578891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1044896636713245985543709 391836238767467244578891)
    ·
      refine ⟨587754358151200866868337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391836238767467244578891 587754358151200866868337)
      ·
        refine ⟨440815768613400650151253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 587754358151200866868337 440815768613400650151253)
        ·
          refine ⟨161431555888696527155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 440815768613400650151253 161431555888696527155)
          ·
            rfl

theorem cell22_114594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 13].length) (baseStart_114594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114594 prefixEnd_114594 := by exact prefixLift 114594
  have htrace : WordTrace (prefixWord ++ tailWord_114594) baseStart_114594 baseEnd_114594 := by
    simpa [prefixWord, tailWord_114594, baseEnd_114594] using wordTrace_append hprefix tailTrace_114594
  have hstable : (prefixWord ++ tailWord_114594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114594).length < 2 ^ (prefixWord ++ tailWord_114594).sum := by decide
  have hdescent : baseEnd_114594 < baseStart_114594 := by decide
  rcases family_descends (prefixWord ++ tailWord_114594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114596 : List Nat := [2, 3, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_114596 : Nat := 118140960795 + 114596 * 2 ^ 59
def prefixEnd_114596 : Nat := 4983230072969 + 3 ^ 40 * 114596 * 2
def baseEnd_114596 : Nat := 39228552721825917548659

theorem tailTrace_114596 : CollatzResearch.WordTrace tailWord_114596 prefixEnd_114596 39228552721825917548659 := by
  unfold tailWord_114596
  simp only [CollatzResearch.WordTrace]
  refine ⟨2089829746422869141873821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2786439661897158855831761 2089829746422869141873821)
  ·
    refine ⟨783686154908575928202683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2089829746422869141873821 783686154908575928202683)
    ·
      refine ⟨1175529232362863892304025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 783686154908575928202683 1175529232362863892304025)
      ·
        refine ⟨881646924272147919228019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1175529232362863892304025 881646924272147919228019)
        ·
          refine ⟨1322470386408221878842029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 881646924272147919228019 1322470386408221878842029)
          ·
            refine ⟨495926394903083204565761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1322470386408221878842029 495926394903083204565761)
            ·
              refine ⟨371944796177312403424321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495926394903083204565761 371944796177312403424321)
              ·
                refine ⟨278958597132984302568241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371944796177312403424321 278958597132984302568241)
                ·
                  refine ⟨209218947849738226926181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278958597132984302568241 209218947849738226926181)
                  ·
                    refine ⟨39228552721825917548659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 209218947849738226926181 39228552721825917548659)
                    ·
                      rfl

theorem cell22_114596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_114596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114596 prefixEnd_114596 := by exact prefixLift 114596
  have htrace : WordTrace (prefixWord ++ tailWord_114596) baseStart_114596 baseEnd_114596 := by
    simpa [prefixWord, tailWord_114596, baseEnd_114596] using wordTrace_append hprefix tailTrace_114596
  have hstable : (prefixWord ++ tailWord_114596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114596).length < 2 ^ (prefixWord ++ tailWord_114596).sum := by decide
  have hdescent : baseEnd_114596 < baseStart_114596 := by decide
  rcases family_descends (prefixWord ++ tailWord_114596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114624 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 2, 6]
def baseStart_114624 : Nat := 118140960795 + 114624 * 2 ^ 59
def prefixEnd_114624 : Nat := 4983230072969 + 3 ^ 40 * 114624 * 2
def baseEnd_114624 : Nat := 39238137694043177848573

theorem tailTrace_114624 : CollatzResearch.WordTrace tailWord_114624 prefixEnd_114624 39238137694043177848573 := by
  unfold tailWord_114624
  simp only [CollatzResearch.WordTrace]
  refine ⟨2090340368372149532883463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2787120491162866043844617 2090340368372149532883463)
  ·
    refine ⟨3135510552558224299325195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2090340368372149532883463 3135510552558224299325195)
    ·
      refine ⟨4703265828837336448987793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3135510552558224299325195 4703265828837336448987793)
      ·
        refine ⟨3527449371628002336740845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4703265828837336448987793 3527449371628002336740845)
        ·
          refine ⟨1322793514360500876277817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3527449371628002336740845 1322793514360500876277817)
          ·
            refine ⟨992095135770375657208363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1322793514360500876277817 992095135770375657208363)
            ·
              refine ⟨1488142703655563485812545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 992095135770375657208363 1488142703655563485812545)
              ·
                refine ⟨1116107027741672614359409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1488142703655563485812545 1116107027741672614359409)
                ·
                  refine ⟨837080270806254460769557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1116107027741672614359409 837080270806254460769557)
                  ·
                    refine ⟨39238137694043177848573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 837080270806254460769557 39238137694043177848573)
                    ·
                      rfl

theorem cell22_114624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_114624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114624 prefixEnd_114624 := by exact prefixLift 114624
  have htrace : WordTrace (prefixWord ++ tailWord_114624) baseStart_114624 baseEnd_114624 := by
    simpa [prefixWord, tailWord_114624, baseEnd_114624] using wordTrace_append hprefix tailTrace_114624
  have hstable : (prefixWord ++ tailWord_114624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114624).length < 2 ^ (prefixWord ++ tailWord_114624).sum := by decide
  have hdescent : baseEnd_114624 < baseStart_114624 := by decide
  rcases family_descends (prefixWord ++ tailWord_114624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114639 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 7]
def baseStart_114639 : Nat := 118140960795 + 114639 * 2 ^ 59
def prefixEnd_114639 : Nat := 4983230072969 + 3 ^ 40 * 114639 * 2
def baseEnd_114639 : Nat := 13081090833529379574509

theorem tailTrace_114639 : CollatzResearch.WordTrace tailWord_114639 prefixEnd_114639 13081090833529379574509 := by
  unfold tailWord_114639
  simp only [CollatzResearch.WordTrace]
  refine ⟨4181227831689956627562971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2787485221126637751708647 4181227831689956627562971)
  ·
    refine ⟨6271841747534934941344457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4181227831689956627562971 6271841747534934941344457)
    ·
      refine ⟨4703881310651201206008343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6271841747534934941344457 4703881310651201206008343)
      ·
        refine ⟨7055821965976801809012515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4703881310651201206008343 7055821965976801809012515)
        ·
          refine ⟨10583732948965202713518773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7055821965976801809012515 10583732948965202713518773)
          ·
            refine ⟨992224963965487754392385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10583732948965202713518773 992224963965487754392385)
            ·
              refine ⟨744168722974115815794289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 992224963965487754392385 744168722974115815794289)
              ·
                refine ⟨558126542230586861845717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 744168722974115815794289 558126542230586861845717)
                ·
                  refine ⟨13081090833529379574509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 558126542230586861845717 13081090833529379574509)
                  ·
                    rfl

theorem cell22_114639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 7].length) (baseStart_114639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114639 prefixEnd_114639 := by exact prefixLift 114639
  have htrace : WordTrace (prefixWord ++ tailWord_114639) baseStart_114639 baseEnd_114639 := by
    simpa [prefixWord, tailWord_114639, baseEnd_114639] using wordTrace_append hprefix tailTrace_114639
  have hstable : (prefixWord ++ tailWord_114639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114639).length < 2 ^ (prefixWord ++ tailWord_114639).sum := by decide
  have hdescent : baseEnd_114639 < baseStart_114639 := by decide
  rcases family_descends (prefixWord ++ tailWord_114639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114748 : List Nat := [2, 2, 2, 2, 2, 1, 4, 1, 2, 4]
def baseStart_114748 : Nat := 118140960795 + 114748 * 2 ^ 59
def prefixEnd_114748 : Nat := 4983230072969 + 3 ^ 40 * 114748 * 2
def baseEnd_114748 : Nat := 39280585428148187748193

theorem tailTrace_114748 : CollatzResearch.WordTrace tailWord_114748 prefixEnd_114748 39280585428148187748193 := by
  unfold tailWord_114748
  simp only [CollatzResearch.WordTrace]
  refine ⟨2092601694147534121640449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2790135592196712162187265 2092601694147534121640449)
  ·
    refine ⟨1569451270610650591230337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2092601694147534121640449 1569451270610650591230337)
    ·
      refine ⟨1177088452957987943422753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1569451270610650591230337 1177088452957987943422753)
      ·
        refine ⟨882816339718490957567065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1177088452957987943422753 882816339718490957567065)
        ·
          refine ⟨662112254788868218175299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 882816339718490957567065 662112254788868218175299)
          ·
            refine ⟨993168382183302327262949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662112254788868218175299 993168382183302327262949)
            ·
              refine ⟨186219071659369186361803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 993168382183302327262949 186219071659369186361803)
              ·
                refine ⟨279328607489053779542705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186219071659369186361803 279328607489053779542705)
                ·
                  refine ⟨209496455616790334657029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279328607489053779542705 209496455616790334657029)
                  ·
                    refine ⟨39280585428148187748193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 209496455616790334657029 39280585428148187748193)
                    ·
                      rfl

theorem cell22_114748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_114748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114748 prefixEnd_114748 := by exact prefixLift 114748
  have htrace : WordTrace (prefixWord ++ tailWord_114748) baseStart_114748 baseEnd_114748 := by
    simpa [prefixWord, tailWord_114748, baseEnd_114748] using wordTrace_append hprefix tailTrace_114748
  have hstable : (prefixWord ++ tailWord_114748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114748).length < 2 ^ (prefixWord ++ tailWord_114748).sum := by decide
  have hdescent : baseEnd_114748 < baseStart_114748 := by decide
  rcases family_descends (prefixWord ++ tailWord_114748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114750 : List Nat := [4, 2, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_114750 : Nat := 118140960795 + 114750 * 2 ^ 59
def prefixEnd_114750 : Nat := 4983230072969 + 3 ^ 40 * 114750 * 2
def baseEnd_114750 : Nat := 39281270069020849198187

theorem tailTrace_114750 : CollatzResearch.WordTrace tailWord_114750 prefixEnd_114750 39281270069020849198187 := by
  unfold tailWord_114750
  simp only [CollatzResearch.WordTrace]
  refine ⟨523159541785977823106713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2790184222858548389902469 523159541785977823106713)
  ·
    refine ⟨392369656339483367330035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 523159541785977823106713 392369656339483367330035)
    ·
      refine ⟨588554484509225050995053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392369656339483367330035 588554484509225050995053)
      ·
        refine ⟨220707931690959394123145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 588554484509225050995053 220707931690959394123145)
        ·
          refine ⟨165530948768219545592359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220707931690959394123145 165530948768219545592359)
          ·
            refine ⟨248296423152329318388539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165530948768219545592359 248296423152329318388539)
            ·
              refine ⟨372444634728493977582809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248296423152329318388539 372444634728493977582809)
              ·
                refine ⟨279333476046370483187107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372444634728493977582809 279333476046370483187107)
                ·
                  refine ⟨419000214069555724780661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279333476046370483187107 419000214069555724780661)
                  ·
                    refine ⟨39281270069020849198187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 419000214069555724780661 39281270069020849198187)
                    ·
                      rfl

theorem cell22_114750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_114750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114750 prefixEnd_114750 := by exact prefixLift 114750
  have htrace : WordTrace (prefixWord ++ tailWord_114750) baseStart_114750 baseEnd_114750 := by
    simpa [prefixWord, tailWord_114750, baseEnd_114750] using wordTrace_append hprefix tailTrace_114750
  have hstable : (prefixWord ++ tailWord_114750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114750).length < 2 ^ (prefixWord ++ tailWord_114750).sum := by decide
  have hdescent : baseEnd_114750 < baseStart_114750 := by decide
  rcases family_descends (prefixWord ++ tailWord_114750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114776 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 2, 6]
def baseStart_114776 : Nat := 118140960795 + 114776 * 2 ^ 59
def prefixEnd_114776 : Nat := 4983230072969 + 3 ^ 40 * 114776 * 2
def baseEnd_114776 : Nat := 39290170400365448048107

theorem tailTrace_114776 : CollatzResearch.WordTrace tailWord_114776 prefixEnd_114776 39290170400365448048107 := by
  unfold tailWord_114776
  simp only [CollatzResearch.WordTrace]
  refine ⟨2093112316096814512650091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2790816421462419350200121 2093112316096814512650091)
  ·
    refine ⟨3139668474145221768975137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2093112316096814512650091 3139668474145221768975137)
    ·
      refine ⟨2354751355608916326731353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3139668474145221768975137 2354751355608916326731353)
      ·
        refine ⟨1766063516706687245048515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2354751355608916326731353 1766063516706687245048515)
        ·
          refine ⟨2649095275060030867572773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766063516706687245048515 2649095275060030867572773)
          ·
            refine ⟨496705364073755787669895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2649095275060030867572773 496705364073755787669895)
            ·
              refine ⟨745058046110633681504843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496705364073755787669895 745058046110633681504843)
              ·
                refine ⟨1117587069165950522257265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745058046110633681504843 1117587069165950522257265)
                ·
                  refine ⟨838190301874462891692949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1117587069165950522257265 838190301874462891692949)
                  ·
                    refine ⟨39290170400365448048107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 838190301874462891692949 39290170400365448048107)
                    ·
                      rfl

theorem cell22_114776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_114776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114776 prefixEnd_114776 := by exact prefixLift 114776
  have htrace : WordTrace (prefixWord ++ tailWord_114776) baseStart_114776 baseEnd_114776 := by
    simpa [prefixWord, tailWord_114776, baseEnd_114776] using wordTrace_append hprefix tailTrace_114776
  have hstable : (prefixWord ++ tailWord_114776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114776).length < 2 ^ (prefixWord ++ tailWord_114776).sum := by decide
  have hdescent : baseEnd_114776 < baseStart_114776 := by decide
  rcases family_descends (prefixWord ++ tailWord_114776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114778 : List Nat := [3, 1, 1, 2, 1, 1, 4, 3, 3, 3]
def baseStart_114778 : Nat := 118140960795 + 114778 * 2 ^ 59
def prefixEnd_114778 : Nat := 4983230072969 + 3 ^ 40 * 114778 * 2
def baseEnd_114778 : Nat := 39290855041238109498101

theorem tailTrace_114778 : CollatzResearch.WordTrace tailWord_114778 prefixEnd_114778 39290855041238109498101 := by
  unfold tailWord_114778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1046574394546595841718247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2790865052124255577915325 1046574394546595841718247)
  ·
    refine ⟨1569861591819893762577371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1046574394546595841718247 1569861591819893762577371)
    ·
      refine ⟨2354792387729840643866057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1569861591819893762577371 2354792387729840643866057)
      ·
        refine ⟨1766094290797380482899543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2354792387729840643866057 1766094290797380482899543)
        ·
          refine ⟨2649141436196070724349315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766094290797380482899543 2649141436196070724349315)
          ·
            refine ⟨3973712154294106086523973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2649141436196070724349315 3973712154294106086523973)
            ·
              refine ⟨745071028930144891223245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3973712154294106086523973 745071028930144891223245)
              ·
                refine ⟨279401635848804334208717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 745071028930144891223245 279401635848804334208717)
                ·
                  refine ⟨104775613443301625328269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279401635848804334208717 104775613443301625328269)
                  ·
                    refine ⟨39290855041238109498101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104775613443301625328269 39290855041238109498101)
                    ·
                      rfl

theorem cell22_114778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_114778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114778 prefixEnd_114778 := by exact prefixLift 114778
  have htrace : WordTrace (prefixWord ++ tailWord_114778) baseStart_114778 baseEnd_114778 := by
    simpa [prefixWord, tailWord_114778, baseEnd_114778] using wordTrace_append hprefix tailTrace_114778
  have hstable : (prefixWord ++ tailWord_114778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114778).length < 2 ^ (prefixWord ++ tailWord_114778).sum := by decide
  have hdescent : baseEnd_114778 < baseStart_114778 := by decide
  rcases family_descends (prefixWord ++ tailWord_114778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114812 : List Nat := [2, 2, 2, 1, 1, 5, 2, 3, 1, 3]
def baseStart_114812 : Nat := 118140960795 + 114812 * 2 ^ 59
def prefixEnd_114812 : Nat := 4983230072969 + 3 ^ 40 * 114812 * 2
def baseEnd_114812 : Nat := 39302493936073354147997

theorem tailTrace_114812 : CollatzResearch.WordTrace tailWord_114812 prefixEnd_114812 39302493936073354147997 := by
  unfold tailWord_114812
  simp only [CollatzResearch.WordTrace]
  refine ⟨2093768830031603586805345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2791691773375471449073793 2093768830031603586805345)
  ·
    refine ⟨1570326622523702690104009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2093768830031603586805345 1570326622523702690104009)
    ·
      refine ⟨1177744966892777017578007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1570326622523702690104009 1177744966892777017578007)
      ·
        refine ⟨1766617450339165526367011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177744966892777017578007 1766617450339165526367011)
        ·
          refine ⟨2649926175508748289550517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766617450339165526367011 2649926175508748289550517)
          ·
            refine ⟨248430578953945152145361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2649926175508748289550517 248430578953945152145361)
            ·
              refine ⟨186322934215458864109021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248430578953945152145361 186322934215458864109021)
              ·
                refine ⟨69871100330797074040883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186322934215458864109021 69871100330797074040883)
                ·
                  refine ⟨104806650496195611061325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69871100330797074040883 104806650496195611061325)
                  ·
                    refine ⟨39302493936073354147997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104806650496195611061325 39302493936073354147997)
                    ·
                      rfl

theorem cell22_114812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_114812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114812 prefixEnd_114812 := by exact prefixLift 114812
  have htrace : WordTrace (prefixWord ++ tailWord_114812) baseStart_114812 baseEnd_114812 := by
    simpa [prefixWord, tailWord_114812, baseEnd_114812] using wordTrace_append hprefix tailTrace_114812
  have hstable : (prefixWord ++ tailWord_114812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114812).length < 2 ^ (prefixWord ++ tailWord_114812).sum := by decide
  have hdescent : baseEnd_114812 < baseStart_114812 := by decide
  rcases family_descends (prefixWord ++ tailWord_114812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114842 : List Nat := [3, 1, 1, 5, 2, 1, 3, 1, 5]
def baseStart_114842 : Nat := 118140960795 + 114842 * 2 ^ 59
def prefixEnd_114842 : Nat := 4983230072969 + 3 ^ 40 * 114842 * 2
def baseEnd_114842 : Nat := 13104254516387758632635

theorem tailTrace_114842 : CollatzResearch.WordTrace tailWord_114842 prefixEnd_114842 13104254516387758632635 := by
  unfold tailWord_114842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1047157962488630574300695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2792421233303014864801853 1047157962488630574300695)
  ·
    refine ⟨1570736943732945861451043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1047157962488630574300695 1570736943732945861451043)
    ·
      refine ⟨2356105415599418792176565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1570736943732945861451043 2356105415599418792176565)
      ·
        refine ⟨220884882712445511766553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2356105415599418792176565 220884882712445511766553)
        ·
          refine ⟨165663662034334133824915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220884882712445511766553 165663662034334133824915)
          ·
            refine ⟨248495493051501200737373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165663662034334133824915 248495493051501200737373)
            ·
              refine ⟨93185809894312950276515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248495493051501200737373 93185809894312950276515)
              ·
                refine ⟨139778714841469425414773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93185809894312950276515 139778714841469425414773)
                ·
                  refine ⟨13104254516387758632635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139778714841469425414773 13104254516387758632635)
                  ·
                    rfl

theorem cell22_114842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_114842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114842 prefixEnd_114842 := by exact prefixLift 114842
  have htrace : WordTrace (prefixWord ++ tailWord_114842) baseStart_114842 baseEnd_114842 := by
    simpa [prefixWord, tailWord_114842, baseEnd_114842] using wordTrace_append hprefix tailTrace_114842
  have hstable : (prefixWord ++ tailWord_114842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114842).length < 2 ^ (prefixWord ++ tailWord_114842).sum := by decide
  have hdescent : baseEnd_114842 < baseStart_114842 := by decide
  rcases family_descends (prefixWord ++ tailWord_114842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114898 : List Nat := [3, 2, 2, 2, 1, 2, 1, 9]
def baseStart_114898 : Nat := 118140960795 + 114898 * 2 ^ 59
def prefixEnd_114898 : Nat := 4983230072969 + 3 ^ 40 * 114898 * 2
def baseEnd_114898 : Nat := 4370214832621977388637

theorem tailTrace_114898 : CollatzResearch.WordTrace tailWord_114898 prefixEnd_114898 4370214832621977388637 := by
  unfold tailWord_114898
  simp only [CollatzResearch.WordTrace]
  refine ⟨1047668584437910965310337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2793782891834429240827565 1047668584437910965310337)
  ·
    refine ⟨785751438328433223982753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1047668584437910965310337 785751438328433223982753)
    ·
      refine ⟨589313578746324917987065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 785751438328433223982753 589313578746324917987065)
      ·
        refine ⟨441985184059743688490299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589313578746324917987065 441985184059743688490299)
        ·
          refine ⟨662977776089615532735449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441985184059743688490299 662977776089615532735449)
          ·
            refine ⟨497233332067211649551587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 662977776089615532735449 497233332067211649551587)
            ·
              refine ⟨745849998100817474327381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497233332067211649551587 745849998100817474327381)
              ·
                refine ⟨4370214832621977388637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 745849998100817474327381 4370214832621977388637)
                ·
                  rfl

theorem cell22_114898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 9].length) (baseStart_114898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114898 prefixEnd_114898 := by exact prefixLift 114898
  have htrace : WordTrace (prefixWord ++ tailWord_114898) baseStart_114898 baseEnd_114898 := by
    simpa [prefixWord, tailWord_114898, baseEnd_114898] using wordTrace_append hprefix tailTrace_114898
  have hstable : (prefixWord ++ tailWord_114898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114898).length < 2 ^ (prefixWord ++ tailWord_114898).sum := by decide
  have hdescent : baseEnd_114898 < baseStart_114898 := by decide
  rcases family_descends (prefixWord ++ tailWord_114898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114947 : List Nat := [1, 1, 1, 3, 2, 3, 3, 4, 1, 3]
def baseStart_114947 : Nat := 118140960795 + 114947 * 2 ^ 59
def prefixEnd_114947 : Nat := 4983230072969 + 3 ^ 40 * 114947 * 2
def baseEnd_114947 : Nat := 39348707194978002022583

theorem tailTrace_114947 : CollatzResearch.WordTrace tailWord_114947 prefixEnd_114947 39348707194978002022583 := by
  unfold tailWord_114947
  simp only [CollatzResearch.WordTrace]
  refine ⟨4192461514574125229775095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2794974343049416819850063 4192461514574125229775095)
  ·
    refine ⟨6288692271861187844662643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4192461514574125229775095 6288692271861187844662643)
    ·
      refine ⟨9433038407791781766993965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6288692271861187844662643 9433038407791781766993965)
      ·
        refine ⟨3537389402921918162622737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9433038407791781766993965 3537389402921918162622737)
        ·
          refine ⟨2653042052191438621967053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3537389402921918162622737 2653042052191438621967053)
          ·
            refine ⟨994890769571789483237645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2653042052191438621967053 994890769571789483237645)
            ·
              refine ⟨373084038589421056214117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 994890769571789483237645 373084038589421056214117)
              ·
                refine ⟨69953257235516448040147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 373084038589421056214117 69953257235516448040147)
                ·
                  refine ⟨104929885853274672060221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69953257235516448040147 104929885853274672060221)
                  ·
                    refine ⟨39348707194978002022583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104929885853274672060221 39348707194978002022583)
                    ·
                      rfl

theorem cell22_114947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 1, 3].length) (baseStart_114947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114947 prefixEnd_114947 := by exact prefixLift 114947
  have htrace : WordTrace (prefixWord ++ tailWord_114947) baseStart_114947 baseEnd_114947 := by
    simpa [prefixWord, tailWord_114947, baseEnd_114947] using wordTrace_append hprefix tailTrace_114947
  have hstable : (prefixWord ++ tailWord_114947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114947).length < 2 ^ (prefixWord ++ tailWord_114947).sum := by decide
  have hdescent : baseEnd_114947 < baseStart_114947 := by decide
  rcases family_descends (prefixWord ++ tailWord_114947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114994 : List Nat := [3, 2, 1, 1, 6, 1, 1, 2, 5]
def baseStart_114994 : Nat := 118140960795 + 114994 * 2 ^ 59
def prefixEnd_114994 : Nat := 4983230072969 + 3 ^ 40 * 114994 * 2
def baseEnd_114994 : Nat := 13121598751828515365813

theorem tailTrace_114994 : CollatzResearch.WordTrace tailWord_114994 prefixEnd_114994 13121598751828515365813 := by
  unfold tailWord_114994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1048543936350963064184009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2796117163602568171157357 1048543936350963064184009)
  ·
    refine ⟨786407952263222298138007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1048543936350963064184009 786407952263222298138007)
    ·
      refine ⟨1179611928394833447207011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 786407952263222298138007 1179611928394833447207011)
      ·
        refine ⟨1769417892592250170810517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1179611928394833447207011 1769417892592250170810517)
        ·
          refine ⟨82941463715261726756743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1769417892592250170810517 82941463715261726756743)
          ·
            refine ⟨124412195572892590135115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82941463715261726756743 124412195572892590135115)
            ·
              refine ⟨186618293359338885202673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124412195572892590135115 186618293359338885202673)
              ·
                refine ⟨139963720019504163902005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186618293359338885202673 139963720019504163902005)
                ·
                  refine ⟨13121598751828515365813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139963720019504163902005 13121598751828515365813)
                  ·
                    rfl

theorem cell22_114994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_114994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_114994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_114994 prefixEnd_114994 := by exact prefixLift 114994
  have htrace : WordTrace (prefixWord ++ tailWord_114994) baseStart_114994 baseEnd_114994 := by
    simpa [prefixWord, tailWord_114994, baseEnd_114994] using wordTrace_append hprefix tailTrace_114994
  have hstable : (prefixWord ++ tailWord_114994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114994).length < 2 ^ (prefixWord ++ tailWord_114994).sum := by decide
  have hdescent : baseEnd_114994 < baseStart_114994 := by decide
  rcases family_descends (prefixWord ++ tailWord_114994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115050 : List Nat := [3, 1, 3, 3, 1, 1, 10]
def baseStart_115050 : Nat := 118140960795 + 115050 * 2 ^ 59
def prefixEnd_115050 : Nat := 4983230072969 + 3 ^ 40 * 115050 * 2
def baseEnd_115050 : Nat := 1458665414811854322121

theorem tailTrace_115050 : CollatzResearch.WordTrace tailWord_115050 prefixEnd_115050 1458665414811854322121 := by
  unfold tailWord_115050
  simp only [CollatzResearch.WordTrace]
  refine ⟨1049054558300243455193651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2797478822133982547183069 1049054558300243455193651)
  ·
    refine ⟨1573581837450365182790477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1049054558300243455193651 1573581837450365182790477)
    ·
      refine ⟨590093189043886943546429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1573581837450365182790477 590093189043886943546429)
      ·
        refine ⟨221284945891457603829911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 590093189043886943546429 221284945891457603829911)
        ·
          refine ⟨331927418837186405744867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221284945891457603829911 331927418837186405744867)
          ·
            refine ⟨497891128255779608617301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331927418837186405744867 497891128255779608617301)
            ·
              refine ⟨1458665414811854322121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 497891128255779608617301 1458665414811854322121)
              ·
                rfl

theorem cell22_115050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 10].length) (baseStart_115050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115050 prefixEnd_115050 := by exact prefixLift 115050
  have htrace : WordTrace (prefixWord ++ tailWord_115050) baseStart_115050 baseEnd_115050 := by
    simpa [prefixWord, tailWord_115050, baseEnd_115050] using wordTrace_append hprefix tailTrace_115050
  have hstable : (prefixWord ++ tailWord_115050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115050).length < 2 ^ (prefixWord ++ tailWord_115050).sum := by decide
  have hdescent : baseEnd_115050 < baseStart_115050 := by decide
  rcases family_descends (prefixWord ++ tailWord_115050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115052 : List Nat := [2, 2, 1, 1, 6, 1, 1, 2, 2, 4]
def baseStart_115052 : Nat := 118140960795 + 115052 * 2 ^ 59
def prefixEnd_115052 : Nat := 4983230072969 + 3 ^ 40 * 115052 * 2
def baseEnd_115052 : Nat := 39384650840792728147261

theorem tailTrace_115052 : CollatzResearch.WordTrace tailWord_115052 prefixEnd_115052 39384650840792728147261 := by
  unfold tailWord_115052
  simp only [CollatzResearch.WordTrace]
  refine ⟨2098145589596864081173705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2797527452795818774898273 2098145589596864081173705)
  ·
    refine ⟨1573609192197648060880279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2098145589596864081173705 1573609192197648060880279)
    ·
      refine ⟨2360413788296472091320419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1573609192197648060880279 2360413788296472091320419)
      ·
        refine ⟨3540620682444708136980629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2360413788296472091320419 3540620682444708136980629)
        ·
          refine ⟨165966594489595693920967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3540620682444708136980629 165966594489595693920967)
          ·
            refine ⟨248949891734393540881451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165966594489595693920967 248949891734393540881451)
            ·
              refine ⟨373424837601590311322177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248949891734393540881451 373424837601590311322177)
              ·
                refine ⟨280068628201192733491633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373424837601590311322177 280068628201192733491633)
                ·
                  refine ⟨210051471150894550118725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280068628201192733491633 210051471150894550118725)
                  ·
                    refine ⟨39384650840792728147261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 210051471150894550118725 39384650840792728147261)
                    ·
                      rfl

theorem cell22_115052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_115052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115052 prefixEnd_115052 := by exact prefixLift 115052
  have htrace : WordTrace (prefixWord ++ tailWord_115052) baseStart_115052 baseEnd_115052 := by
    simpa [prefixWord, tailWord_115052, baseEnd_115052] using wordTrace_append hprefix tailTrace_115052
  have hstable : (prefixWord ++ tailWord_115052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115052).length < 2 ^ (prefixWord ++ tailWord_115052).sum := by decide
  have hdescent : baseEnd_115052 < baseStart_115052 := by decide
  rcases family_descends (prefixWord ++ tailWord_115052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115185 : List Nat := [1, 2, 2, 2, 3, 1, 2, 9]
def baseStart_115185 : Nat := 118140960795 + 115185 * 2 ^ 59
def prefixEnd_115185 : Nat := 4983230072969 + 3 ^ 40 * 115185 * 2
def baseEnd_115185 : Nat := 4381131050980523841317

theorem tailTrace_115185 : CollatzResearch.WordTrace tailWord_115185 prefixEnd_115185 4381131050980523841317 := by
  unfold tailWord_115185
  simp only [CollatzResearch.WordTrace]
  refine ⟨4201142087711891876939009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2800761391807927917959339 4201142087711891876939009)
  ·
    refine ⟨3150856565783918907704257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4201142087711891876939009 3150856565783918907704257)
    ·
      refine ⟨2363142424337939180778193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3150856565783918907704257 2363142424337939180778193)
      ·
        refine ⟨1772356818253454385583645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2363142424337939180778193 1772356818253454385583645)
        ·
          refine ⟨664633806845045394593867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1772356818253454385583645 664633806845045394593867)
          ·
            refine ⟨996950710267568091890801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664633806845045394593867 996950710267568091890801)
            ·
              refine ⟨747713032700676068918101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 996950710267568091890801 747713032700676068918101)
              ·
                refine ⟨4381131050980523841317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 747713032700676068918101 4381131050980523841317)
                ·
                  rfl

theorem cell22_115185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 9].length) (baseStart_115185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115185 prefixEnd_115185 := by exact prefixLift 115185
  have htrace : WordTrace (prefixWord ++ tailWord_115185) baseStart_115185 baseEnd_115185 := by
    simpa [prefixWord, tailWord_115185, baseEnd_115185] using wordTrace_append hprefix tailTrace_115185
  have hstable : (prefixWord ++ tailWord_115185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115185).length < 2 ^ (prefixWord ++ tailWord_115185).sum := by decide
  have hdescent : baseEnd_115185 < baseStart_115185 := by decide
  rcases family_descends (prefixWord ++ tailWord_115185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115309 : List Nat := [1, 5, 1, 1, 3, 2, 1, 2, 6]
def baseStart_115309 : Nat := 118140960795 + 115309 * 2 ^ 59
def prefixEnd_115309 : Nat := 4983230072969 + 3 ^ 40 * 115309 * 2
def baseEnd_115309 : Nat := 13157542397643241490491

theorem tailTrace_115309 : CollatzResearch.WordTrace tailWord_115309 prefixEnd_115309 13157542397643241490491 := by
  unfold tailWord_115309
  simp only [CollatzResearch.WordTrace]
  refine ⟨4205664739262661054452981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2803776492841774036301987 4205664739262661054452981)
  ·
    refine ⟨394281069305874473854967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4205664739262661054452981 394281069305874473854967)
    ·
      refine ⟨591421603958811710782451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394281069305874473854967 591421603958811710782451)
      ·
        refine ⟨887132405938217566173677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591421603958811710782451 887132405938217566173677)
        ·
          refine ⟨332674652226831587315129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 887132405938217566173677 332674652226831587315129)
          ·
            refine ⟨249505989170123690486347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332674652226831587315129 249505989170123690486347)
            ·
              refine ⟨374258983755185535729521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249505989170123690486347 374258983755185535729521)
              ·
                refine ⟨280694237816389151797141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374258983755185535729521 280694237816389151797141)
                ·
                  refine ⟨13157542397643241490491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 280694237816389151797141 13157542397643241490491)
                  ·
                    rfl

theorem cell22_115309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_115309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115309 prefixEnd_115309 := by exact prefixLift 115309
  have htrace : WordTrace (prefixWord ++ tailWord_115309) baseStart_115309 baseEnd_115309 := by
    simpa [prefixWord, tailWord_115309, baseEnd_115309] using wordTrace_append hprefix tailTrace_115309
  have hstable : (prefixWord ++ tailWord_115309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115309).length < 2 ^ (prefixWord ++ tailWord_115309).sum := by decide
  have hdescent : baseEnd_115309 < baseStart_115309 := by decide
  rcases family_descends (prefixWord ++ tailWord_115309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115416 : List Nat := [2, 1, 2, 2, 3, 2, 4, 1, 5]
def baseStart_115416 : Nat := 118140960795 + 115416 * 2 ^ 59
def prefixEnd_115416 : Nat := 4983230072969 + 3 ^ 40 * 115416 * 2
def baseEnd_115416 : Nat := 13169751826539037348715

theorem tailTrace_115416 : CollatzResearch.WordTrace tailWord_115416 prefixEnd_115416 13169751826539037348715 := by
  unfold tailWord_115416
  simp only [CollatzResearch.WordTrace]
  refine ⟨2104783674937509164299051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2806378233250012219065401 2104783674937509164299051)
  ·
    refine ⟨3157175512406263746448577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2104783674937509164299051 3157175512406263746448577)
    ·
      refine ⟨2367881634304697809836433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3157175512406263746448577 2367881634304697809836433)
      ·
        refine ⟨1775911225728523357377325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2367881634304697809836433 1775911225728523357377325)
        ·
          refine ⟨665966709648196259016497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1775911225728523357377325 665966709648196259016497)
          ·
            refine ⟨499475032236147194262373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 665966709648196259016497 499475032236147194262373)
            ·
              refine ⟨93651568544277598924195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 499475032236147194262373 93651568544277598924195)
              ·
                refine ⟨140477352816416398386293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93651568544277598924195 140477352816416398386293)
                ·
                  refine ⟨13169751826539037348715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140477352816416398386293 13169751826539037348715)
                  ·
                    rfl

theorem cell22_115416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 5].length) (baseStart_115416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115416 prefixEnd_115416 := by exact prefixLift 115416
  have htrace : WordTrace (prefixWord ++ tailWord_115416) baseStart_115416 baseEnd_115416 := by
    simpa [prefixWord, tailWord_115416, baseEnd_115416] using wordTrace_append hprefix tailTrace_115416
  have hstable : (prefixWord ++ tailWord_115416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115416).length < 2 ^ (prefixWord ++ tailWord_115416).sum := by decide
  have hdescent : baseEnd_115416 < baseStart_115416 := by decide
  rcases family_descends (prefixWord ++ tailWord_115416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115510 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_115510 : Nat := 118140960795 + 115510 * 2 ^ 59
def prefixEnd_115510 : Nat := 4983230072969 + 3 ^ 40 * 115510 * 2
def baseEnd_115510 : Nat := 39541433600632200195857

theorem tailTrace_115510 : CollatzResearch.WordTrace tailWord_115510 prefixEnd_115510 39541433600632200195857 := by
  unfold tailWord_115510
  simp only [CollatzResearch.WordTrace]
  refine ⟨263312238220904523907499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2808663874356314921679989 263312238220904523907499)
  ·
    refine ⟨394968357331356785861249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263312238220904523907499 394968357331356785861249)
    ·
      refine ⟨296226267998517589395937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394968357331356785861249 296226267998517589395937)
      ·
        refine ⟨222169700998888192046953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296226267998517589395937 222169700998888192046953)
        ·
          refine ⟨166627275749166144035215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222169700998888192046953 166627275749166144035215)
          ·
            refine ⟨249940913623749216052823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166627275749166144035215 249940913623749216052823)
            ·
              refine ⟨374911370435623824079235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249940913623749216052823 374911370435623824079235)
              ·
                refine ⟨562367055653435736118853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374911370435623824079235 562367055653435736118853)
                ·
                  refine ⟨105443822935019200522285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 562367055653435736118853 105443822935019200522285)
                  ·
                    refine ⟨39541433600632200195857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105443822935019200522285 39541433600632200195857)
                    ·
                      rfl

theorem cell22_115510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_115510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115510 prefixEnd_115510 := by exact prefixLift 115510
  have htrace : WordTrace (prefixWord ++ tailWord_115510) baseStart_115510 baseEnd_115510 := by
    simpa [prefixWord, tailWord_115510, baseEnd_115510] using wordTrace_append hprefix tailTrace_115510
  have hstable : (prefixWord ++ tailWord_115510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115510).length < 2 ^ (prefixWord ++ tailWord_115510).sum := by decide
  have hdescent : baseEnd_115510 < baseStart_115510 := by decide
  rcases family_descends (prefixWord ++ tailWord_115510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115540 : List Nat := [2, 4, 1, 1, 5, 1, 2, 6]
def baseStart_115540 : Nat := 118140960795 + 115540 * 2 ^ 59
def prefixEnd_115540 : Nat := 4983230072969 + 3 ^ 40 * 115540 * 2
def baseEnd_115540 : Nat := 4394633690413569105085

theorem tailTrace_115540 : CollatzResearch.WordTrace tailWord_115540 prefixEnd_115540 4394633690413569105085 := by
  unfold tailWord_115540
  simp only [CollatzResearch.WordTrace]
  refine ⟨2107045000712893753056037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2809393334283858337408049 2107045000712893753056037)
  ·
    refine ⟨395070937633667578698007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2107045000712893753056037 395070937633667578698007)
    ·
      refine ⟨592606406450501368047011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395070937633667578698007 592606406450501368047011)
      ·
        refine ⟨888909609675752052070517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592606406450501368047011 888909609675752052070517)
        ·
          refine ⟨83335275907101754881611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 888909609675752052070517 83335275907101754881611)
          ·
            refine ⟨125002913860652632322417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83335275907101754881611 125002913860652632322417)
            ·
              refine ⟨93752185395489474241813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125002913860652632322417 93752185395489474241813)
              ·
                refine ⟨4394633690413569105085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93752185395489474241813 4394633690413569105085)
                ·
                  rfl

theorem cell22_115540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 6].length) (baseStart_115540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115540 prefixEnd_115540 := by exact prefixLift 115540
  have htrace : WordTrace (prefixWord ++ tailWord_115540) baseStart_115540 baseEnd_115540 := by
    simpa [prefixWord, tailWord_115540, baseEnd_115540] using wordTrace_append hprefix tailTrace_115540
  have hstable : (prefixWord ++ tailWord_115540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115540).length < 2 ^ (prefixWord ++ tailWord_115540).sum := by decide
  have hdescent : baseEnd_115540 < baseStart_115540 := by decide
  rcases family_descends (prefixWord ++ tailWord_115540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115555 : List Nat := [1, 1, 1, 5, 3, 1, 3, 3, 1, 3]
def baseStart_115555 : Nat := 118140960795 + 115555 * 2 ^ 59
def prefixEnd_115555 : Nat := 4983230072969 + 3 ^ 40 * 115555 * 2
def baseEnd_115555 : Nat := 39556838020267082820719

theorem tailTrace_115555 : CollatzResearch.WordTrace tailWord_115555 prefixEnd_115555 39556838020267082820719 := by
  unfold tailWord_115555
  simp only [CollatzResearch.WordTrace]
  refine ⟨4214637096371445067908119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2809758064247630045272079 4214637096371445067908119)
  ·
    refine ⟨6321955644557167601862179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4214637096371445067908119 6321955644557167601862179)
    ·
      refine ⟨9482933466835751402793269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6321955644557167601862179 9482933466835751402793269)
      ·
        refine ⟨889025012515851694011869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9482933466835751402793269 889025012515851694011869)
        ·
          refine ⟨333384379693444385254451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 889025012515851694011869 333384379693444385254451)
          ·
            refine ⟨500076569540166577881677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333384379693444385254451 500076569540166577881677)
            ·
              refine ⟨187528713577562466705629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 500076569540166577881677 187528713577562466705629)
              ·
                refine ⟨70323267591585925014611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187528713577562466705629 70323267591585925014611)
                ·
                  refine ⟨105484901387378887521917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70323267591585925014611 105484901387378887521917)
                  ·
                    refine ⟨39556838020267082820719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105484901387378887521917 39556838020267082820719)
                    ·
                      rfl

theorem cell22_115555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 1, 3].length) (baseStart_115555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115555 prefixEnd_115555 := by exact prefixLift 115555
  have htrace : WordTrace (prefixWord ++ tailWord_115555) baseStart_115555 baseEnd_115555 := by
    simpa [prefixWord, tailWord_115555, baseEnd_115555] using wordTrace_append hprefix tailTrace_115555
  have hstable : (prefixWord ++ tailWord_115555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115555).length < 2 ^ (prefixWord ++ tailWord_115555).sum := by decide
  have hdescent : baseEnd_115555 < baseStart_115555 := by decide
  rcases family_descends (prefixWord ++ tailWord_115555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115613 : List Nat := [1, 4, 2, 1, 2, 1, 2, 5, 4]
def baseStart_115613 : Nat := 118140960795 + 115613 * 2 ^ 59
def prefixEnd_115613 : Nat := 4983230072969 + 3 ^ 40 * 115613 * 2
def baseEnd_115613 : Nat := 13192230868524754956847

theorem tailTrace_115613 : CollatzResearch.WordTrace tailWord_115613 prefixEnd_115613 13192230868524754956847 := by
  unfold tailWord_115613
  simp only [CollatzResearch.WordTrace]
  refine ⟨4216752530161320973519493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2811168353440880649012995 4216752530161320973519493)
  ·
    refine ⟨790641099405247682534905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4216752530161320973519493 790641099405247682534905)
    ·
      refine ⟨592980824553935761901179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 790641099405247682534905 592980824553935761901179)
      ·
        refine ⟨889471236830903642851769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592980824553935761901179 889471236830903642851769)
        ·
          refine ⟨667103427623177732138827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 889471236830903642851769 667103427623177732138827)
          ·
            refine ⟨1000655141434766598208241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667103427623177732138827 1000655141434766598208241)
            ·
              refine ⟨750491356076074948656181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1000655141434766598208241 750491356076074948656181)
              ·
                refine ⟨70358564632132026436517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 750491356076074948656181 70358564632132026436517)
                ·
                  refine ⟨13192230868524754956847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70358564632132026436517 13192230868524754956847)
                  ·
                    rfl

theorem cell22_115613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_115613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115613 prefixEnd_115613 := by exact prefixLift 115613
  have htrace : WordTrace (prefixWord ++ tailWord_115613) baseStart_115613 baseEnd_115613 := by
    simpa [prefixWord, tailWord_115613, baseEnd_115613] using wordTrace_append hprefix tailTrace_115613
  have hstable : (prefixWord ++ tailWord_115613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115613).length < 2 ^ (prefixWord ++ tailWord_115613).sum := by decide
  have hdescent : baseEnd_115613 < baseStart_115613 := by decide
  rcases family_descends (prefixWord ++ tailWord_115613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115615 : List Nat := [1, 1, 2, 5, 2, 2, 3, 1, 1, 4]
def baseStart_115615 : Nat := 118140960795 + 115615 * 2 ^ 59
def prefixEnd_115615 : Nat := 4983230072969 + 3 ^ 40 * 115615 * 2
def baseEnd_115615 : Nat := 39577377246446926320535

theorem tailTrace_115615 : CollatzResearch.WordTrace tailWord_115615 prefixEnd_115615 39577377246446926320535 := by
  unfold tailWord_115615
  simp only [CollatzResearch.WordTrace]
  refine ⟨4216825476154075315092299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2811216984102716876728199 4216825476154075315092299)
  ·
    refine ⟨6325238214231112972638449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4216825476154075315092299 6325238214231112972638449)
    ·
      refine ⟨4743928660673334729478837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6325238214231112972638449 4743928660673334729478837)
      ·
        refine ⟨444743311938125130888641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4743928660673334729478837 444743311938125130888641)
        ·
          refine ⟨333557483953593848166481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444743311938125130888641 333557483953593848166481)
          ·
            refine ⟨250168112965195386124861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333557483953593848166481 250168112965195386124861)
            ·
              refine ⟨93813042361948269796823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250168112965195386124861 93813042361948269796823)
              ·
                refine ⟨140719563542922404695235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93813042361948269796823 140719563542922404695235)
                ·
                  refine ⟨211079345314383607042853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140719563542922404695235 211079345314383607042853)
                  ·
                    refine ⟨39577377246446926320535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 211079345314383607042853 39577377246446926320535)
                    ·
                      rfl

theorem cell22_115615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 1, 4].length) (baseStart_115615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115615 prefixEnd_115615 := by exact prefixLift 115615
  have htrace : WordTrace (prefixWord ++ tailWord_115615) baseStart_115615 baseEnd_115615 := by
    simpa [prefixWord, tailWord_115615, baseEnd_115615] using wordTrace_append hprefix tailTrace_115615
  have hstable : (prefixWord ++ tailWord_115615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115615).length < 2 ^ (prefixWord ++ tailWord_115615).sum := by decide
  have hdescent : baseEnd_115615 < baseStart_115615 := by decide
  rcases family_descends (prefixWord ++ tailWord_115615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115641 : List Nat := [1, 2, 1, 4, 2, 2, 3, 7]
def baseStart_115641 : Nat := 118140960795 + 115641 * 2 ^ 59
def prefixEnd_115641 : Nat := 4983230072969 + 3 ^ 40 * 115641 * 2
def baseEnd_115641 : Nat := 4398475286421280574495

theorem tailTrace_115641 : CollatzResearch.WordTrace tailWord_115641 prefixEnd_115641 4398475286421280574495 := by
  unfold tailWord_115641
  simp only [CollatzResearch.WordTrace]
  refine ⟨4217773774059881755538777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2811849182706587837025851 4217773774059881755538777)
  ·
    refine ⟨3163330330544911316654083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4217773774059881755538777 3163330330544911316654083)
    ·
      refine ⟨4744995495817366974981125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3163330330544911316654083 4744995495817366974981125)
      ·
        refine ⟨889686655465756307808961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4744995495817366974981125 889686655465756307808961)
        ·
          refine ⟨667264991599317230856721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 889686655465756307808961 667264991599317230856721)
          ·
            refine ⟨500448743699487923142541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667264991599317230856721 500448743699487923142541)
            ·
              refine ⟨187668278887307971178453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 500448743699487923142541 187668278887307971178453)
              ·
                refine ⟨4398475286421280574495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 187668278887307971178453 4398475286421280574495)
                ·
                  rfl

theorem cell22_115641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 7].length) (baseStart_115641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115641 prefixEnd_115641 := by exact prefixLift 115641
  have htrace : WordTrace (prefixWord ++ tailWord_115641) baseStart_115641 baseEnd_115641 := by
    simpa [prefixWord, tailWord_115641, baseEnd_115641] using wordTrace_append hprefix tailTrace_115641
  have hstable : (prefixWord ++ tailWord_115641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115641).length < 2 ^ (prefixWord ++ tailWord_115641).sum := by decide
  have hdescent : baseEnd_115641 < baseStart_115641 := by decide
  rcases family_descends (prefixWord ++ tailWord_115641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115690 : List Nat := [3, 1, 3, 1, 2, 3, 2, 1, 3, 3]
def baseStart_115690 : Nat := 118140960795 + 115690 * 2 ^ 59
def prefixEnd_115690 : Nat := 4983230072969 + 3 ^ 40 * 115690 * 2
def baseEnd_115690 : Nat := 39603051279171730695305

theorem tailTrace_115690 : CollatzResearch.WordTrace tailWord_115690 prefixEnd_115690 39603051279171730695305 := by
  unfold tailWord_115690
  simp only [CollatzResearch.WordTrace]
  refine ⟨1054890237720590781018131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2813040633921575416048349 1054890237720590781018131)
  ·
    refine ⟨1582335356580886171527197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1054890237720590781018131 1582335356580886171527197)
    ·
      refine ⟨593375758717832314322699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1582335356580886171527197 593375758717832314322699)
      ·
        refine ⟨890063638076748471484049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593375758717832314322699 890063638076748471484049)
        ·
          refine ⟨667547728557561353613037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 890063638076748471484049 667547728557561353613037)
          ·
            refine ⟨250330398209085507604889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 667547728557561353613037 250330398209085507604889)
            ·
              refine ⟨187747798656814130703667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250330398209085507604889 187747798656814130703667)
              ·
                refine ⟨281621697985221196055501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187747798656814130703667 281621697985221196055501)
                ·
                  refine ⟨105608136744457948520813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281621697985221196055501 105608136744457948520813)
                  ·
                    refine ⟨39603051279171730695305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105608136744457948520813 39603051279171730695305)
                    ·
                      rfl

theorem cell22_115690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_115690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115690 prefixEnd_115690 := by exact prefixLift 115690
  have htrace : WordTrace (prefixWord ++ tailWord_115690) baseStart_115690 baseEnd_115690 := by
    simpa [prefixWord, tailWord_115690, baseEnd_115690] using wordTrace_append hprefix tailTrace_115690
  have hstable : (prefixWord ++ tailWord_115690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115690).length < 2 ^ (prefixWord ++ tailWord_115690).sum := by decide
  have hdescent : baseEnd_115690 < baseStart_115690 := by decide
  rcases family_descends (prefixWord ++ tailWord_115690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115754 : List Nat := [3, 1, 4, 1, 4, 1, 2, 1, 5]
def baseStart_115754 : Nat := 118140960795 + 115754 * 2 ^ 59
def prefixEnd_115754 : Nat := 4983230072969 + 3 ^ 40 * 115754 * 2
def baseEnd_115754 : Nat := 13208319929032299031703

theorem tailTrace_115754 : CollatzResearch.WordTrace tailWord_115754 prefixEnd_115754 13208319929032299031703 := by
  unfold tailWord_115754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055473805662625513600579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2814596815100334702934877 1055473805662625513600579)
  ·
    refine ⟨1583210708493938270400869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1055473805662625513600579 1583210708493938270400869)
    ·
      refine ⟨296852007842613425700163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1583210708493938270400869 296852007842613425700163)
      ·
        refine ⟨445278011763920138550245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296852007842613425700163 445278011763920138550245)
        ·
          refine ⟨83489627205735025978171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 445278011763920138550245 83489627205735025978171)
          ·
            refine ⟨125234440808602538967257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83489627205735025978171 125234440808602538967257)
            ·
              refine ⟨93925830606451904225443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125234440808602538967257 93925830606451904225443)
              ·
                refine ⟨140888745909677856338165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93925830606451904225443 140888745909677856338165)
                ·
                  refine ⟨13208319929032299031703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140888745909677856338165 13208319929032299031703)
                  ·
                    rfl

theorem cell22_115754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_115754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115754 prefixEnd_115754 := by exact prefixLift 115754
  have htrace : WordTrace (prefixWord ++ tailWord_115754) baseStart_115754 baseEnd_115754 := by
    simpa [prefixWord, tailWord_115754, baseEnd_115754] using wordTrace_append hprefix tailTrace_115754
  have hstable : (prefixWord ++ tailWord_115754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115754).length < 2 ^ (prefixWord ++ tailWord_115754).sum := by decide
  have hdescent : baseEnd_115754 < baseStart_115754 := by decide
  rcases family_descends (prefixWord ++ tailWord_115754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115776 : List Nat := [2, 1, 1, 2, 2, 3, 1, 10]
def baseStart_115776 : Nat := 118140960795 + 115776 * 2 ^ 59
def prefixEnd_115776 : Nat := 4983230072969 + 3 ^ 40 * 115776 * 2
def baseEnd_115776 : Nat := 4403610092966241449449

theorem tailTrace_115776 : CollatzResearch.WordTrace tailWord_115776 prefixEnd_115776 4403610092966241449449 := by
  unfold tailWord_115776
  simp only [CollatzResearch.WordTrace]
  refine ⟨2111348814285399905851591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2815131752380533207802121 2111348814285399905851591)
  ·
    refine ⟨3167023221428099858777387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2111348814285399905851591 3167023221428099858777387)
    ·
      refine ⟨4750534832142149788166081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3167023221428099858777387 4750534832142149788166081)
      ·
        refine ⟨3562901124106612341124561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4750534832142149788166081 3562901124106612341124561)
        ·
          refine ⟨2672175843079959255843421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3562901124106612341124561 2672175843079959255843421)
          ·
            refine ⟨1002065941154984720941283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2672175843079959255843421 1002065941154984720941283)
            ·
              refine ⟨1503098911732477081411925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1002065941154984720941283 1503098911732477081411925)
              ·
                refine ⟨4403610092966241449449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1503098911732477081411925 4403610092966241449449)
                ·
                  rfl

theorem cell22_115776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 10].length) (baseStart_115776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115776 prefixEnd_115776 := by exact prefixLift 115776
  have htrace : WordTrace (prefixWord ++ tailWord_115776) baseStart_115776 baseEnd_115776 := by
    simpa [prefixWord, tailWord_115776, baseEnd_115776] using wordTrace_append hprefix tailTrace_115776
  have hstable : (prefixWord ++ tailWord_115776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115776).length < 2 ^ (prefixWord ++ tailWord_115776).sum := by decide
  have hdescent : baseEnd_115776 < baseStart_115776 := by decide
  rcases family_descends (prefixWord ++ tailWord_115776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115810 : List Nat := [3, 3, 2, 2, 1, 1, 3, 7]
def baseStart_115810 : Nat := 118140960795 + 115810 * 2 ^ 59
def prefixEnd_115810 : Nat := 4983230072969 + 3 ^ 40 * 115810 * 2
def baseEnd_115810 : Nat := 4404903303503490854993

theorem tailTrace_115810 : CollatzResearch.WordTrace tailWord_115810 prefixEnd_115810 4404903303503490854993 := by
  unfold tailWord_115810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055984427611905904610221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2815958473631749078960589 1055984427611905904610221)
  ·
    refine ⟨395994160354464714228833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1055984427611905904610221 395994160354464714228833)
    ·
      refine ⟨296995620265848535671625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395994160354464714228833 296995620265848535671625)
      ·
        refine ⟨222746715199386401753719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296995620265848535671625 222746715199386401753719)
        ·
          refine ⟨334120072799079602630579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222746715199386401753719 334120072799079602630579)
          ·
            refine ⟨501180109198619403945869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334120072799079602630579 501180109198619403945869)
            ·
              refine ⟨187942540949482276479701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 501180109198619403945869 187942540949482276479701)
              ·
                refine ⟨4404903303503490854993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 187942540949482276479701 4404903303503490854993)
                ·
                  rfl

theorem cell22_115810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 7].length) (baseStart_115810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115810 prefixEnd_115810 := by exact prefixLift 115810
  have htrace : WordTrace (prefixWord ++ tailWord_115810) baseStart_115810 baseEnd_115810 := by
    simpa [prefixWord, tailWord_115810, baseEnd_115810] using wordTrace_append hprefix tailTrace_115810
  have hstable : (prefixWord ++ tailWord_115810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115810).length < 2 ^ (prefixWord ++ tailWord_115810).sum := by decide
  have hdescent : baseEnd_115810 < baseStart_115810 := by decide
  rcases family_descends (prefixWord ++ tailWord_115810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115829 : List Nat := [1, 3, 4, 3, 1, 2, 1, 1, 2, 4]
def baseStart_115829 : Nat := 118140960795 + 115829 * 2 ^ 59
def prefixEnd_115829 : Nat := 4983230072969 + 3 ^ 40 * 115829 * 2
def baseEnd_115829 : Nat := 39650633819821701469879

theorem tailTrace_115829 : CollatzResearch.WordTrace tailWord_115829 prefixEnd_115829 39650633819821701469879 := by
  unfold tailWord_115829
  simp only [CollatzResearch.WordTrace]
  refine ⟨4224630697378789863382541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2816420464919193242255027 4224630697378789863382541)
  ·
    refine ⟨1584236511517046198768453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4224630697378789863382541 1584236511517046198768453)
    ·
      refine ⟨297044345909446162269085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1584236511517046198768453 297044345909446162269085)
      ·
        refine ⟨111391629716042310850907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297044345909446162269085 111391629716042310850907)
        ·
          refine ⟨167087444574063466276361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111391629716042310850907 167087444574063466276361)
          ·
            refine ⟨125315583430547599707271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167087444574063466276361 125315583430547599707271)
            ·
              refine ⟨187973375145821399560907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125315583430547599707271 187973375145821399560907)
              ·
                refine ⟨281960062718732099341361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187973375145821399560907 281960062718732099341361)
                ·
                  refine ⟨211470047039049074506021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281960062718732099341361 211470047039049074506021)
                  ·
                    refine ⟨39650633819821701469879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 211470047039049074506021 39650633819821701469879)
                    ·
                      rfl

theorem cell22_115829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_115829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115829 prefixEnd_115829 := by exact prefixLift 115829
  have htrace : WordTrace (prefixWord ++ tailWord_115829) baseStart_115829 baseEnd_115829 := by
    simpa [prefixWord, tailWord_115829, baseEnd_115829] using wordTrace_append hprefix tailTrace_115829
  have hstable : (prefixWord ++ tailWord_115829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115829).length < 2 ^ (prefixWord ++ tailWord_115829).sum := by decide
  have hdescent : baseEnd_115829 < baseStart_115829 := by decide
  rcases family_descends (prefixWord ++ tailWord_115829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115898 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 3, 5]
def baseStart_115898 : Nat := 118140960795 + 115898 * 2 ^ 59
def prefixEnd_115898 : Nat := 4983230072969 + 3 ^ 40 * 115898 * 2
def baseEnd_115898 : Nat := 39674253929928521494667

theorem tailTrace_115898 : CollatzResearch.WordTrace tailWord_115898 prefixEnd_115898 39674253929928521494667 := by
  unfold tailWord_115898
  simp only [CollatzResearch.WordTrace]
  refine ⟨1056786833532203661911087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2818098222752543098429565 1056786833532203661911087)
  ·
    refine ⟨1585180250298305492866631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1056786833532203661911087 1585180250298305492866631)
    ·
      refine ⟨2377770375447458239299947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1585180250298305492866631 2377770375447458239299947)
      ·
        refine ⟨3566655563171187358949921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2377770375447458239299947 3566655563171187358949921)
        ·
          refine ⟨2674991672378390519212441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3566655563171187358949921 2674991672378390519212441)
          ·
            refine ⟨2006243754283792889409331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2674991672378390519212441 2006243754283792889409331)
            ·
              refine ⟨3009365631425689334113997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006243754283792889409331 3009365631425689334113997)
              ·
                refine ⟨1128512111784633500292749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3009365631425689334113997 1128512111784633500292749)
                ·
                  refine ⟨423192041919237562609781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1128512111784633500292749 423192041919237562609781)
                  ·
                    refine ⟨39674253929928521494667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 423192041919237562609781 39674253929928521494667)
                    ·
                      rfl

theorem cell22_115898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_115898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115898 prefixEnd_115898 := by exact prefixLift 115898
  have htrace : WordTrace (prefixWord ++ tailWord_115898) baseStart_115898 baseEnd_115898 := by
    simpa [prefixWord, tailWord_115898, baseEnd_115898] using wordTrace_append hprefix tailTrace_115898
  have hstable : (prefixWord ++ tailWord_115898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115898).length < 2 ^ (prefixWord ++ tailWord_115898).sum := by decide
  have hdescent : baseEnd_115898 < baseStart_115898 := by decide
  rcases family_descends (prefixWord ++ tailWord_115898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115902 : List Nat := [4, 2, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_115902 : Nat := 118140960795 + 115902 * 2 ^ 59
def prefixEnd_115902 : Nat := 4983230072969 + 3 ^ 40 * 115902 * 2
def baseEnd_115902 : Nat := 39675623211673844394655

theorem tailTrace_115902 : CollatzResearch.WordTrace tailWord_115902 prefixEnd_115902 39675623211673844394655 := by
  unfold tailWord_115902
  simp only [CollatzResearch.WordTrace]
  refine ⟨528411653264290416348745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2818195484076215553859973 528411653264290416348745)
  ·
    refine ⟨396308739948217812261559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 528411653264290416348745 396308739948217812261559)
    ·
      refine ⟨594463109922326718392339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396308739948217812261559 594463109922326718392339)
      ·
        refine ⟨891694664883490077588509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594463109922326718392339 891694664883490077588509)
        ·
          refine ⟨334385499331308779095691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 891694664883490077588509 334385499331308779095691)
          ·
            refine ⟨501578248996963168643537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334385499331308779095691 501578248996963168643537)
            ·
              refine ⟨376183686747722376482653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501578248996963168643537 376183686747722376482653)
              ·
                refine ⟨141068882530395891180995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 376183686747722376482653 141068882530395891180995)
                ·
                  refine ⟨211603323795593836771493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141068882530395891180995 211603323795593836771493)
                  ·
                    refine ⟨39675623211673844394655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 211603323795593836771493 39675623211673844394655)
                    ·
                      rfl

theorem cell22_115902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_115902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115902 prefixEnd_115902 := by exact prefixLift 115902
  have htrace : WordTrace (prefixWord ++ tailWord_115902) baseStart_115902 baseEnd_115902 := by
    simpa [prefixWord, tailWord_115902, baseEnd_115902] using wordTrace_append hprefix tailTrace_115902
  have hstable : (prefixWord ++ tailWord_115902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115902).length < 2 ^ (prefixWord ++ tailWord_115902).sum := by decide
  have hdescent : baseEnd_115902 < baseStart_115902 := by decide
  rcases family_descends (prefixWord ++ tailWord_115902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115910 : List Nat := [6, 1, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_115910 : Nat := 118140960795 + 115910 * 2 ^ 59
def prefixEnd_115910 : Nat := 4983230072969 + 3 ^ 40 * 115910 * 2
def baseEnd_115910 : Nat := 39678361775164490194631

theorem tailTrace_115910 : CollatzResearch.WordTrace tailWord_115910 prefixEnd_115910 39678361775164490194631 := by
  unfold tailWord_115910
  simp only [CollatzResearch.WordTrace]
  refine ⟨132112031565166896783787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2818390006723560464720789 132112031565166896783787)
  ·
    refine ⟨198168047347750345175681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132112031565166896783787 198168047347750345175681)
    ·
      refine ⟨148626035510812758881761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198168047347750345175681 148626035510812758881761)
      ·
        refine ⟨111469526633109569161321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148626035510812758881761 111469526633109569161321)
        ·
          refine ⟨83602144974832176870991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111469526633109569161321 83602144974832176870991)
          ·
            refine ⟨125403217462248265306487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83602144974832176870991 125403217462248265306487)
            ·
              refine ⟨188104826193372397959731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125403217462248265306487 188104826193372397959731)
              ·
                refine ⟨282157239290058596939597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188104826193372397959731 282157239290058596939597)
                ·
                  refine ⟨105808964733771973852349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282157239290058596939597 105808964733771973852349)
                  ·
                    refine ⟨39678361775164490194631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105808964733771973852349 39678361775164490194631)
                    ·
                      rfl

theorem cell22_115910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_115910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115910 prefixEnd_115910 := by exact prefixLift 115910
  have htrace : WordTrace (prefixWord ++ tailWord_115910) baseStart_115910 baseEnd_115910 := by
    simpa [prefixWord, tailWord_115910, baseEnd_115910] using wordTrace_append hprefix tailTrace_115910
  have hstable : (prefixWord ++ tailWord_115910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115910).length < 2 ^ (prefixWord ++ tailWord_115910).sum := by decide
  have hdescent : baseEnd_115910 < baseStart_115910 := by decide
  rcases family_descends (prefixWord ++ tailWord_115910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115998 : List Nat := [4, 3, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_115998 : Nat := 118140960795 + 115998 * 2 ^ 59
def prefixEnd_115998 : Nat := 4983230072969 + 3 ^ 40 * 115998 * 2
def baseEnd_115998 : Nat := 39708485973561593994361

theorem tailTrace_115998 : CollatzResearch.WordTrace tailWord_115998 prefixEnd_115998 39708485973561593994361 := by
  unfold tailWord_115998
  simp only [CollatzResearch.WordTrace]
  refine ⟨528849329220816465785581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2820529755844354484189765 528849329220816465785581)
  ·
    refine ⟨198318498457806174669593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 528849329220816465785581 198318498457806174669593)
    ·
      refine ⟨148738873843354631002195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198318498457806174669593 148738873843354631002195)
      ·
        refine ⟨223108310765031946503293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148738873843354631002195 223108310765031946503293)
        ·
          refine ⟨83665616536886979938735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223108310765031946503293 83665616536886979938735)
          ·
            refine ⟨125498424805330469908103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83665616536886979938735 125498424805330469908103)
            ·
              refine ⟨188247637207995704862155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125498424805330469908103 188247637207995704862155)
              ·
                refine ⟨282371455811993557293233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188247637207995704862155 282371455811993557293233)
                ·
                  refine ⟨211778591858995167969925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282371455811993557293233 211778591858995167969925)
                  ·
                    refine ⟨39708485973561593994361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 211778591858995167969925 39708485973561593994361)
                    ·
                      rfl

theorem cell22_115998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_115998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_115998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_115998 prefixEnd_115998 := by exact prefixLift 115998
  have htrace : WordTrace (prefixWord ++ tailWord_115998) baseStart_115998 baseEnd_115998 := by
    simpa [prefixWord, tailWord_115998, baseEnd_115998] using wordTrace_append hprefix tailTrace_115998
  have hstable : (prefixWord ++ tailWord_115998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115998).length < 2 ^ (prefixWord ++ tailWord_115998).sum := by decide
  have hdescent : baseEnd_115998 < baseStart_115998 := by decide
  rcases family_descends (prefixWord ++ tailWord_115998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116065 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 6, 4]
def baseStart_116065 : Nat := 118140960795 + 116065 * 2 ^ 59
def prefixEnd_116065 : Nat := 4983230072969 + 3 ^ 40 * 116065 * 2
def baseEnd_116065 : Nat := 39731421442795752569155

theorem tailTrace_116065 : CollatzResearch.WordTrace tailWord_116065 prefixEnd_116065 39731421442795752569155 := by
  unfold tailWord_116065
  simp only [CollatzResearch.WordTrace]
  refine ⟨4233238324523802168973649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2822158883015868112649099 4233238324523802168973649)
  ·
    refine ⟨3174928743392851626730237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4233238324523802168973649 3174928743392851626730237)
    ·
      refine ⟨1190598278772319360023839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3174928743392851626730237 1190598278772319360023839)
      ·
        refine ⟨1785897418158479040035759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1190598278772319360023839 1785897418158479040035759)
        ·
          refine ⟨2678846127237718560053639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1785897418158479040035759 2678846127237718560053639)
          ·
            refine ⟨4018269190856577840080459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2678846127237718560053639 4018269190856577840080459)
            ·
              refine ⟨6027403786284866760120689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4018269190856577840080459 6027403786284866760120689)
              ·
                refine ⟨4520552839713650070090517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6027403786284866760120689 4520552839713650070090517)
                ·
                  refine ⟨211900914361577347035493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4520552839713650070090517 211900914361577347035493)
                  ·
                    refine ⟨39731421442795752569155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 211900914361577347035493 39731421442795752569155)
                    ·
                      rfl

theorem cell22_116065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_116065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116065 prefixEnd_116065 := by exact prefixLift 116065
  have htrace : WordTrace (prefixWord ++ tailWord_116065) baseStart_116065 baseEnd_116065 := by
    simpa [prefixWord, tailWord_116065, baseEnd_116065] using wordTrace_append hprefix tailTrace_116065
  have hstable : (prefixWord ++ tailWord_116065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116065).length < 2 ^ (prefixWord ++ tailWord_116065).sum := by decide
  have hdescent : baseEnd_116065 < baseStart_116065 := by decide
  rcases family_descends (prefixWord ++ tailWord_116065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116067 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 4, 3]
def baseStart_116067 : Nat := 118140960795 + 116067 * 2 ^ 59
def prefixEnd_116067 : Nat := 4983230072969 + 3 ^ 40 * 116067 * 2
def baseEnd_116067 : Nat := 39732106083668414019149

theorem tailTrace_116067 : CollatzResearch.WordTrace tailWord_116067 prefixEnd_116067 39732106083668414019149 := by
  unfold tailWord_116067
  simp only [CollatzResearch.WordTrace]
  refine ⟨4233311270516556510546455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2822207513677704340364303 4233311270516556510546455)
  ·
    refine ⟨6349966905774834765819683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4233311270516556510546455 6349966905774834765819683)
    ·
      refine ⟨9524950358662252148729525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6349966905774834765819683 9524950358662252148729525)
      ·
        refine ⟨892964096124586138943393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9524950358662252148729525 892964096124586138943393)
        ·
          refine ⟨669723072093439604207545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 892964096124586138943393 669723072093439604207545)
          ·
            refine ⟨502292304070079703155659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 669723072093439604207545 502292304070079703155659)
            ·
              refine ⟨753438456105119554733489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502292304070079703155659 753438456105119554733489)
              ·
                refine ⟨565078842078839666050117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 753438456105119554733489 565078842078839666050117)
                ·
                  refine ⟨105952282889782437384397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 565078842078839666050117 105952282889782437384397)
                  ·
                    refine ⟨39732106083668414019149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105952282889782437384397 39732106083668414019149)
                    ·
                      rfl

theorem cell22_116067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 3].length) (baseStart_116067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116067 prefixEnd_116067 := by exact prefixLift 116067
  have htrace : WordTrace (prefixWord ++ tailWord_116067) baseStart_116067 baseEnd_116067 := by
    simpa [prefixWord, tailWord_116067, baseEnd_116067] using wordTrace_append hprefix tailTrace_116067
  have hstable : (prefixWord ++ tailWord_116067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116067).length < 2 ^ (prefixWord ++ tailWord_116067).sum := by decide
  have hdescent : baseEnd_116067 < baseStart_116067 := by decide
  rcases family_descends (prefixWord ++ tailWord_116067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116082 : List Nat := [3, 2, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_116082 : Nat := 118140960795 + 116082 * 2 ^ 59
def prefixEnd_116082 : Nat := 4983230072969 + 3 ^ 40 * 116082 * 2
def baseEnd_116082 : Nat := 39737240890213374894103

theorem tailTrace_116082 : CollatzResearch.WordTrace tailWord_116082 prefixEnd_116082 39737240890213374894103 := by
  unfold tailWord_116082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1058464591365553518085625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2822572243641476048228333 1058464591365553518085625)
  ·
    refine ⟨793848443524165138564219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1058464591365553518085625 793848443524165138564219)
    ·
      refine ⟨1190772665286247707846329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 793848443524165138564219 1190772665286247707846329)
      ·
        refine ⟨893079498964685780884747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1190772665286247707846329 893079498964685780884747)
        ·
          refine ⟨1339619248447028671327121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893079498964685780884747 1339619248447028671327121)
          ·
            refine ⟨1004714436335271503495341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1339619248447028671327121 1004714436335271503495341)
            ·
              refine ⟨376767913625726813810753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1004714436335271503495341 376767913625726813810753)
              ·
                refine ⟨282575935219295110358065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376767913625726813810753 282575935219295110358065)
                ·
                  refine ⟨211931951414471332768549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282575935219295110358065 211931951414471332768549)
                  ·
                    refine ⟨39737240890213374894103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 211931951414471332768549 39737240890213374894103)
                    ·
                      rfl

theorem cell22_116082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_116082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116082 prefixEnd_116082 := by exact prefixLift 116082
  have htrace : WordTrace (prefixWord ++ tailWord_116082) baseStart_116082 baseEnd_116082 := by
    simpa [prefixWord, tailWord_116082, baseEnd_116082] using wordTrace_append hprefix tailTrace_116082
  have hstable : (prefixWord ++ tailWord_116082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116082).length < 2 ^ (prefixWord ++ tailWord_116082).sum := by decide
  have hdescent : baseEnd_116082 < baseStart_116082 := by decide
  rcases family_descends (prefixWord ++ tailWord_116082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116157 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_116157 : Nat := 118140960795 + 116157 * 2 ^ 59
def prefixEnd_116157 : Nat := 4983230072969 + 3 ^ 40 * 116157 * 2
def baseEnd_116157 : Nat := 39762914922938179268873

theorem tailTrace_116157 : CollatzResearch.WordTrace tailWord_116157 prefixEnd_116157 39762914922938179268873 := by
  unfold tailWord_116157
  simp only [CollatzResearch.WordTrace]
  refine ⟨4236593840190501881322725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2824395893460334587548483 4236593840190501881322725)
  ·
    refine ⟨794361345035719102748011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4236593840190501881322725 794361345035719102748011)
    ·
      refine ⟨1191542017553578654122017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 794361345035719102748011 1191542017553578654122017)
      ·
        refine ⟨893656513165183990591513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1191542017553578654122017 893656513165183990591513)
        ·
          refine ⟨670242384873887992943635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 893656513165183990591513 670242384873887992943635)
          ·
            refine ⟨1005363577310831989415453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670242384873887992943635 1005363577310831989415453)
            ·
              refine ⟨377011341491561996030795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1005363577310831989415453 377011341491561996030795)
              ·
                refine ⟨565517012237342994046193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377011341491561996030795 565517012237342994046193)
                ·
                  refine ⟨424137759178007245534645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565517012237342994046193 424137759178007245534645)
                  ·
                    refine ⟨39762914922938179268873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 424137759178007245534645 39762914922938179268873)
                    ·
                      rfl

theorem cell22_116157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_116157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116157 prefixEnd_116157 := by exact prefixLift 116157
  have htrace : WordTrace (prefixWord ++ tailWord_116157) baseStart_116157 baseEnd_116157 := by
    simpa [prefixWord, tailWord_116157, baseEnd_116157] using wordTrace_append hprefix tailTrace_116157
  have hstable : (prefixWord ++ tailWord_116157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116157).length < 2 ^ (prefixWord ++ tailWord_116157).sum := by decide
  have hdescent : baseEnd_116157 < baseStart_116157 := by decide
  rcases family_descends (prefixWord ++ tailWord_116157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116238 : List Nat := [4, 1, 1, 2, 4, 2, 1, 3, 4]
def baseStart_116238 : Nat := 118140960795 + 116238 * 2 ^ 59
def prefixEnd_116238 : Nat := 4983230072969 + 3 ^ 40 * 116238 * 2
def baseEnd_116238 : Nat := 13263547626093655997875

theorem tailTrace_116238 : CollatzResearch.WordTrace tailWord_116238 prefixEnd_116238 13263547626093655997875 := by
  unfold tailWord_116238
  simp only [CollatzResearch.WordTrace]
  refine ⟨529943519112131589377671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2826365435264701810014245 529943519112131589377671)
  ·
    refine ⟨794915278668197384066507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 529943519112131589377671 794915278668197384066507)
    ·
      refine ⟨1192372918002296076099761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 794915278668197384066507 1192372918002296076099761)
      ·
        refine ⟨894279688501722057074821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1192372918002296076099761 894279688501722057074821)
        ·
          refine ⟨167677441594072885701529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 894279688501722057074821 167677441594072885701529)
          ·
            refine ⟨125758081195554664276147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167677441594072885701529 125758081195554664276147)
            ·
              refine ⟨188637121793331996414221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125758081195554664276147 188637121793331996414221)
              ·
                refine ⟨70738920672499498655333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188637121793331996414221 70738920672499498655333)
                ·
                  refine ⟨13263547626093655997875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70738920672499498655333 13263547626093655997875)
                  ·
                    rfl

theorem cell22_116238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_116238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116238 prefixEnd_116238 := by exact prefixLift 116238
  have htrace : WordTrace (prefixWord ++ tailWord_116238) baseStart_116238 baseEnd_116238 := by
    simpa [prefixWord, tailWord_116238, baseEnd_116238] using wordTrace_append hprefix tailTrace_116238
  have hstable : (prefixWord ++ tailWord_116238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116238).length < 2 ^ (prefixWord ++ tailWord_116238).sum := by decide
  have hdescent : baseEnd_116238 < baseStart_116238 := by decide
  rcases family_descends (prefixWord ++ tailWord_116238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116270 : List Nat := [4, 1, 3, 1, 2, 3, 2, 1, 2, 3]
def baseStart_116270 : Nat := 118140960795 + 116270 * 2 ^ 59
def prefixEnd_116270 : Nat := 4983230072969 + 3 ^ 40 * 116270 * 2
def baseEnd_116270 : Nat := 39801597132243551193527

theorem tailTrace_116270 : CollatzResearch.WordTrace tailWord_116270 prefixEnd_116270 39801597132243551193527 := by
  unfold tailWord_116270
  simp only [CollatzResearch.WordTrace]
  refine ⟨530089411097640272523283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2827143525854081453457509 530089411097640272523283)
  ·
    refine ⟨795134116646460408784925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 530089411097640272523283 795134116646460408784925)
    ·
      refine ⟨298175293742422653294347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 795134116646460408784925 298175293742422653294347)
      ·
        refine ⟨447262940613633979941521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298175293742422653294347 447262940613633979941521)
        ·
          refine ⟨335447205460225484956141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447262940613633979941521 335447205460225484956141)
          ·
            refine ⟨125792702047584556858553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335447205460225484956141 125792702047584556858553)
            ·
              refine ⟨94344526535688417643915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125792702047584556858553 94344526535688417643915)
              ·
                refine ⟨141516789803532626465873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94344526535688417643915 141516789803532626465873)
                ·
                  refine ⟨106137592352649469849405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141516789803532626465873 106137592352649469849405)
                  ·
                    refine ⟨39801597132243551193527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106137592352649469849405 39801597132243551193527)
                    ·
                      rfl

theorem cell22_116270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_116270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116270 prefixEnd_116270 := by exact prefixLift 116270
  have htrace : WordTrace (prefixWord ++ tailWord_116270) baseStart_116270 baseEnd_116270 := by
    simpa [prefixWord, tailWord_116270, baseEnd_116270] using wordTrace_append hprefix tailTrace_116270
  have hstable : (prefixWord ++ tailWord_116270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116270).length < 2 ^ (prefixWord ++ tailWord_116270).sum := by decide
  have hdescent : baseEnd_116270 < baseStart_116270 := by decide
  rcases family_descends (prefixWord ++ tailWord_116270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116324 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_116324 : Nat := 118140960795 + 116324 * 2 ^ 59
def prefixEnd_116324 : Nat := 4983230072969 + 3 ^ 40 * 116324 * 2
def baseEnd_116324 : Nat := 39820082435805410343361

theorem tailTrace_116324 : CollatzResearch.WordTrace tailWord_116324 prefixEnd_116324 39820082435805410343361 := by
  unfold tailWord_116324
  simp only [CollatzResearch.WordTrace]
  refine ⟨2121342415292744701326013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2828456553723659601768017 2121342415292744701326013)
  ·
    refine ⟨795503405734779262997255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2121342415292744701326013 795503405734779262997255)
    ·
      refine ⟨1193255108602168894495883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 795503405734779262997255 1193255108602168894495883)
      ·
        refine ⟨1789882662903253341743825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1193255108602168894495883 1789882662903253341743825)
        ·
          refine ⟨1342411997177440006307869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1789882662903253341743825 1342411997177440006307869)
          ·
            refine ⟨503404498941540002365451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1342411997177440006307869 503404498941540002365451)
            ·
              refine ⟨755106748412310003548177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503404498941540002365451 755106748412310003548177)
              ·
                refine ⟨566330061309232502661133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 755106748412310003548177 566330061309232502661133)
                ·
                  refine ⟨212373772990962188497925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 566330061309232502661133 212373772990962188497925)
                  ·
                    refine ⟨39820082435805410343361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 212373772990962188497925 39820082435805410343361)
                    ·
                      rfl

theorem cell22_116324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_116324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116324 prefixEnd_116324 := by exact prefixLift 116324
  have htrace : WordTrace (prefixWord ++ tailWord_116324) baseStart_116324 baseEnd_116324 := by
    simpa [prefixWord, tailWord_116324, baseEnd_116324] using wordTrace_append hprefix tailTrace_116324
  have hstable : (prefixWord ++ tailWord_116324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116324).length < 2 ^ (prefixWord ++ tailWord_116324).sum := by decide
  have hdescent : baseEnd_116324 < baseStart_116324 := by decide
  rcases family_descends (prefixWord ++ tailWord_116324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116341 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 3, 4]
def baseStart_116341 : Nat := 118140960795 + 116341 * 2 ^ 59
def prefixEnd_116341 : Nat := 4983230072969 + 3 ^ 40 * 116341 * 2
def baseEnd_116341 : Nat := 39825901883223032668309

theorem tailTrace_116341 : CollatzResearch.WordTrace tailWord_116341 prefixEnd_116341 39825901883223032668309 := by
  unfold tailWord_116341
  simp only [CollatzResearch.WordTrace]
  refine ⟨4243304871523901306020877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2828869914349267537347251 4243304871523901306020877)
  ·
    refine ⟨1591239326821462989757829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4243304871523901306020877 1591239326821462989757829)
    ·
      refine ⟨298357373779024310579593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1591239326821462989757829 298357373779024310579593)
      ·
        refine ⟨223768030334268232934695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298357373779024310579593 223768030334268232934695)
        ·
          refine ⟨335652045501402349402043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223768030334268232934695 335652045501402349402043)
          ·
            refine ⟨503478068252103524103065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335652045501402349402043 503478068252103524103065)
            ·
              refine ⟨377608551189077643077299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503478068252103524103065 377608551189077643077299)
              ·
                refine ⟨566412826783616464615949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377608551189077643077299 566412826783616464615949)
                ·
                  refine ⟨212404810043856174230981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 566412826783616464615949 212404810043856174230981)
                  ·
                    refine ⟨39825901883223032668309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 212404810043856174230981 39825901883223032668309)
                    ·
                      rfl

theorem cell22_116341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_116341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116341 prefixEnd_116341 := by exact prefixLift 116341
  have htrace : WordTrace (prefixWord ++ tailWord_116341) baseStart_116341 baseEnd_116341 := by
    simpa [prefixWord, tailWord_116341, baseEnd_116341] using wordTrace_append hprefix tailTrace_116341
  have hstable : (prefixWord ++ tailWord_116341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116341).length < 2 ^ (prefixWord ++ tailWord_116341).sum := by decide
  have hdescent : baseEnd_116341 < baseStart_116341 := by decide
  rcases family_descends (prefixWord ++ tailWord_116341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116392 : List Nat := [2, 1, 7, 1, 1, 1, 2, 2, 1, 4]
def baseStart_116392 : Nat := 118140960795 + 116392 * 2 ^ 59
def prefixEnd_116392 : Nat := 4983230072969 + 3 ^ 40 * 116392 * 2
def baseEnd_116392 : Nat := 39843360225475899643153

theorem tailTrace_116392 : CollatzResearch.WordTrace tailWord_116392 prefixEnd_116392 39843360225475899643153 := by
  unfold tailWord_116392
  simp only [CollatzResearch.WordTrace]
  refine ⟨2122582497169568508063715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2830109996226091344084953 2122582497169568508063715)
  ·
    refine ⟨3183873745754352762095573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2122582497169568508063715 3183873745754352762095573)
    ·
      refine ⟨74622040916117642861615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 3183873745754352762095573 74622040916117642861615)
      ·
        refine ⟨111933061374176464292423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74622040916117642861615 111933061374176464292423)
        ·
          refine ⟨167899592061264696438635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111933061374176464292423 167899592061264696438635)
          ·
            refine ⟨251849388091897044657953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167899592061264696438635 251849388091897044657953)
            ·
              refine ⟨188887041068922783493465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251849388091897044657953 188887041068922783493465)
              ·
                refine ⟨141665280801692087620099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188887041068922783493465 141665280801692087620099)
                ·
                  refine ⟨212497921202538131430149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141665280801692087620099 212497921202538131430149)
                  ·
                    refine ⟨39843360225475899643153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 212497921202538131430149 39843360225475899643153)
                    ·
                      rfl

theorem cell22_116392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_116392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116392 prefixEnd_116392 := by exact prefixLift 116392
  have htrace : WordTrace (prefixWord ++ tailWord_116392) baseStart_116392 baseEnd_116392 := by
    simpa [prefixWord, tailWord_116392, baseEnd_116392] using wordTrace_append hprefix tailTrace_116392
  have hstable : (prefixWord ++ tailWord_116392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116392).length < 2 ^ (prefixWord ++ tailWord_116392).sum := by decide
  have hdescent : baseEnd_116392 < baseStart_116392 := by decide
  rcases family_descends (prefixWord ++ tailWord_116392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116433 : List Nat := [1, 2, 2, 1, 2, 6, 1, 1, 3, 3]
def baseStart_116433 : Nat := 118140960795 + 116433 * 2 ^ 59
def prefixEnd_116433 : Nat := 4983230072969 + 3 ^ 40 * 116433 * 2
def baseEnd_116433 : Nat := 39857395363365459368027

theorem tailTrace_116433 : CollatzResearch.WordTrace tailWord_116433 prefixEnd_116433 39857395363365459368027 := by
  unfold tailWord_116433
  simp only [CollatzResearch.WordTrace]
  refine ⟨4246660387190601018369953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2831106924793734012246635 4246660387190601018369953)
  ·
    refine ⟨3184995290392950763777465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4246660387190601018369953 3184995290392950763777465)
    ·
      refine ⟨2388746467794713072833099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3184995290392950763777465 2388746467794713072833099)
      ·
        refine ⟨3583119701692069609249649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2388746467794713072833099 3583119701692069609249649)
        ·
          refine ⟨2687339776269052206937237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3583119701692069609249649 2687339776269052206937237)
          ·
            refine ⟨125969052012611822200183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2687339776269052206937237 125969052012611822200183)
            ·
              refine ⟨188953578018917733300275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125969052012611822200183 188953578018917733300275)
              ·
                refine ⟨283430367028376599950413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188953578018917733300275 283430367028376599950413)
                ·
                  refine ⟨106286387635641224981405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283430367028376599950413 106286387635641224981405)
                  ·
                    refine ⟨39857395363365459368027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106286387635641224981405 39857395363365459368027)
                    ·
                      rfl

theorem cell22_116433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_116433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116433 prefixEnd_116433 := by exact prefixLift 116433
  have htrace : WordTrace (prefixWord ++ tailWord_116433) baseStart_116433 baseEnd_116433 := by
    simpa [prefixWord, tailWord_116433, baseEnd_116433] using wordTrace_append hprefix tailTrace_116433
  have hstable : (prefixWord ++ tailWord_116433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116433).length < 2 ^ (prefixWord ++ tailWord_116433).sum := by decide
  have hdescent : baseEnd_116433 < baseStart_116433 := by decide
  rcases family_descends (prefixWord ++ tailWord_116433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116486 : List Nat := [6, 2, 2, 1, 2, 1, 1, 7]
def baseStart_116486 : Nat := 118140960795 + 116486 * 2 ^ 59
def prefixEnd_116486 : Nat := 4983230072969 + 3 ^ 40 * 116486 * 2
def baseEnd_116486 : Nat := 4430615371832331976985

theorem tailTrace_116486 : CollatzResearch.WordTrace tailWord_116486 prefixEnd_116486 4430615371832331976985 := by
  unfold tailWord_116486
  simp only [CollatzResearch.WordTrace]
  refine ⟨132768545499955970939041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2832395637332394046699541 132768545499955970939041)
  ·
    refine ⟨99576409124966978204281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132768545499955970939041 99576409124966978204281)
    ·
      refine ⟨74682306843725233653211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99576409124966978204281 74682306843725233653211)
      ·
        refine ⟨112023460265587850479817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74682306843725233653211 112023460265587850479817)
        ·
          refine ⟨84017595199190887859863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112023460265587850479817 84017595199190887859863)
          ·
            refine ⟨126026392798786331789795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84017595199190887859863 126026392798786331789795)
            ·
              refine ⟨189039589198179497684693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126026392798786331789795 189039589198179497684693)
              ·
                refine ⟨4430615371832331976985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 189039589198179497684693 4430615371832331976985)
                ·
                  rfl

theorem cell22_116486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_116486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116486 prefixEnd_116486 := by exact prefixLift 116486
  have htrace : WordTrace (prefixWord ++ tailWord_116486) baseStart_116486 baseEnd_116486 := by
    simpa [prefixWord, tailWord_116486, baseEnd_116486] using wordTrace_append hprefix tailTrace_116486
  have hstable : (prefixWord ++ tailWord_116486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116486).length < 2 ^ (prefixWord ++ tailWord_116486).sum := by decide
  have hdescent : baseEnd_116486 < baseStart_116486 := by decide
  rcases family_descends (prefixWord ++ tailWord_116486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116489 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 5, 5]
def baseStart_116489 : Nat := 118140960795 + 116489 * 2 ^ 59
def prefixEnd_116489 : Nat := 4983230072969 + 3 ^ 40 * 116489 * 2
def baseEnd_116489 : Nat := 39876565307799979967855

theorem tailTrace_116489 : CollatzResearch.WordTrace tailWord_116489 prefixEnd_116489 39876565307799979967855 := by
  unfold tailWord_116489
  simp only [CollatzResearch.WordTrace]
  refine ⟨4248702874987722582408521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2832468583325148388272347 4248702874987722582408521)
  ·
    refine ⟨3186527156240791936806391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4248702874987722582408521 3186527156240791936806391)
    ·
      refine ⟨4779790734361187905209587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3186527156240791936806391 4779790734361187905209587)
      ·
        refine ⟨7169686101541781857814381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4779790734361187905209587 7169686101541781857814381)
        ·
          refine ⟨2688632288078168196680393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7169686101541781857814381 2688632288078168196680393)
          ·
            refine ⟨2016474216058626147510295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2688632288078168196680393 2016474216058626147510295)
            ·
              refine ⟨3024711324087939221265443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2016474216058626147510295 3024711324087939221265443)
              ·
                refine ⟨4537066986131908831898165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024711324087939221265443 4537066986131908831898165)
                ·
                  refine ⟨425350029949866452990453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4537066986131908831898165 425350029949866452990453)
                  ·
                    refine ⟨39876565307799979967855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 425350029949866452990453 39876565307799979967855)
                    ·
                      rfl

theorem cell22_116489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_116489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116489 prefixEnd_116489 := by exact prefixLift 116489
  have htrace : WordTrace (prefixWord ++ tailWord_116489) baseStart_116489 baseEnd_116489 := by
    simpa [prefixWord, tailWord_116489, baseEnd_116489] using wordTrace_append hprefix tailTrace_116489
  have hstable : (prefixWord ++ tailWord_116489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116489).length < 2 ^ (prefixWord ++ tailWord_116489).sum := by decide
  have hdescent : baseEnd_116489 < baseStart_116489 := by decide
  rcases family_descends (prefixWord ++ tailWord_116489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116506 : List Nat := [3, 1, 1, 3, 2, 2, 1, 3, 1, 5]
def baseStart_116506 : Nat := 118140960795 + 116506 * 2 ^ 59
def prefixEnd_116506 : Nat := 4983230072969 + 3 ^ 40 * 116506 * 2
def baseEnd_116506 : Nat := 39882384755217602292803

theorem tailTrace_116506 : CollatzResearch.WordTrace tailWord_116506 prefixEnd_116506 39882384755217602292803 := by
  unfold tailWord_116506
  simp only [CollatzResearch.WordTrace]
  refine ⟨1062330728981533621444343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2832881943950756323851581 1062330728981533621444343)
  ·
    refine ⟨1593496093472300432166515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1062330728981533621444343 1593496093472300432166515)
    ·
      refine ⟨2390244140208450648249773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1593496093472300432166515 2390244140208450648249773)
      ·
        refine ⟨896341552578168993093665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2390244140208450648249773 896341552578168993093665)
        ·
          refine ⟨672256164433626744820249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 896341552578168993093665 672256164433626744820249)
          ·
            refine ⟨504192123325220058615187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 672256164433626744820249 504192123325220058615187)
            ·
              refine ⟨756288184987830087922781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504192123325220058615187 756288184987830087922781)
              ·
                refine ⟨283608069370436282971043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 756288184987830087922781 283608069370436282971043)
                ·
                  refine ⟨425412104055654424456565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283608069370436282971043 425412104055654424456565)
                  ·
                    refine ⟨39882384755217602292803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 425412104055654424456565 39882384755217602292803)
                    ·
                      rfl

theorem cell22_116506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_116506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116506 prefixEnd_116506 := by exact prefixLift 116506
  have htrace : WordTrace (prefixWord ++ tailWord_116506) baseStart_116506 baseEnd_116506 := by
    simpa [prefixWord, tailWord_116506, baseEnd_116506] using wordTrace_append hprefix tailTrace_116506
  have hstable : (prefixWord ++ tailWord_116506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116506).length < 2 ^ (prefixWord ++ tailWord_116506).sum := by decide
  have hdescent : baseEnd_116506 < baseStart_116506 := by decide
  rcases family_descends (prefixWord ++ tailWord_116506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116643 : List Nat := [1, 1, 1, 4, 1, 2, 1, 7, 4]
def baseStart_116643 : Nat := 118140960795 + 116643 * 2 ^ 59
def prefixEnd_116643 : Nat := 4983230072969 + 3 ^ 40 * 116643 * 2
def baseEnd_116643 : Nat := 13309760884998303872461

theorem tailTrace_116643 : CollatzResearch.WordTrace tailWord_116643 prefixEnd_116643 13309760884998303872461 := by
  unfold tailWord_116643
  simp only [CollatzResearch.WordTrace]
  refine ⟨4254319716429806883514583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2836213144286537922343055 4254319716429806883514583)
  ·
    refine ⟨6381479574644710325271875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4254319716429806883514583 6381479574644710325271875)
    ·
      refine ⟨9572219361967065487907813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6381479574644710325271875 9572219361967065487907813)
      ·
        refine ⟨1794791130368824778982715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9572219361967065487907813 1794791130368824778982715)
        ·
          refine ⟨2692186695553237168474073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1794791130368824778982715 2692186695553237168474073)
          ·
            refine ⟨2019140021664927876355555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2692186695553237168474073 2019140021664927876355555)
            ·
              refine ⟨3028710032497391814533333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2019140021664927876355555 3028710032497391814533333)
              ·
                refine ⟨70985391386657620653125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3028710032497391814533333 70985391386657620653125)
                ·
                  refine ⟨13309760884998303872461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70985391386657620653125 13309760884998303872461)
                  ·
                    rfl

theorem cell22_116643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 4].length) (baseStart_116643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116643 prefixEnd_116643 := by exact prefixLift 116643
  have htrace : WordTrace (prefixWord ++ tailWord_116643) baseStart_116643 baseEnd_116643 := by
    simpa [prefixWord, tailWord_116643, baseEnd_116643] using wordTrace_append hprefix tailTrace_116643
  have hstable : (prefixWord ++ tailWord_116643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116643).length < 2 ^ (prefixWord ++ tailWord_116643).sum := by decide
  have hdescent : baseEnd_116643 < baseStart_116643 := by decide
  rcases family_descends (prefixWord ++ tailWord_116643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116658 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 4, 3]
def baseStart_116658 : Nat := 118140960795 + 116658 * 2 ^ 59
def prefixEnd_116658 : Nat := 4983230072969 + 3 ^ 40 * 116658 * 2
def baseEnd_116658 : Nat := 39934417461539872492337

theorem tailTrace_116658 : CollatzResearch.WordTrace tailWord_116658 prefixEnd_116658 39934417461539872492337 := by
  unfold tailWord_116658
  simp only [CollatzResearch.WordTrace]
  refine ⟨1063716702843866111327657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2836577874250309630207085 1063716702843866111327657)
  ·
    refine ⟨797787527132899583495743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1063716702843866111327657 797787527132899583495743)
    ·
      refine ⟨1196681290699349375243615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 797787527132899583495743 1196681290699349375243615)
      ·
        refine ⟨1795021936049024062865423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1196681290699349375243615 1795021936049024062865423)
        ·
          refine ⟨2692532904073536094298135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1795021936049024062865423 2692532904073536094298135)
          ·
            refine ⟨4038799356110304141447203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2692532904073536094298135 4038799356110304141447203)
            ·
              refine ⟨6058199034165456212170805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4038799356110304141447203 6058199034165456212170805)
              ·
                refine ⟨567956159453011519891013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6058199034165456212170805 567956159453011519891013)
                ·
                  refine ⟨106491779897439659979565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 567956159453011519891013 106491779897439659979565)
                  ·
                    refine ⟨39934417461539872492337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106491779897439659979565 39934417461539872492337)
                    ·
                      rfl

theorem cell22_116658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_116658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116658 prefixEnd_116658 := by exact prefixLift 116658
  have htrace : WordTrace (prefixWord ++ tailWord_116658) baseStart_116658 baseEnd_116658 := by
    simpa [prefixWord, tailWord_116658, baseEnd_116658] using wordTrace_append hprefix tailTrace_116658
  have hstable : (prefixWord ++ tailWord_116658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116658).length < 2 ^ (prefixWord ++ tailWord_116658).sum := by decide
  have hdescent : baseEnd_116658 < baseStart_116658 := by decide
  rcases family_descends (prefixWord ++ tailWord_116658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116690 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_116690 : Nat := 118140960795 + 116690 * 2 ^ 59
def prefixEnd_116690 : Nat := 4983230072969 + 3 ^ 40 * 116690 * 2
def baseEnd_116690 : Nat := 39945371715502455692239

theorem tailTrace_116690 : CollatzResearch.WordTrace tailWord_116690 prefixEnd_116690 39945371715502455692239 := by
  unfold tailWord_116690
  simp only [CollatzResearch.WordTrace]
  refine ⟨1064008486814883477618881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2837355964839689273650349 1064008486814883477618881)
  ·
    refine ⟨798006365111162608214161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1064008486814883477618881 798006365111162608214161)
    ·
      refine ⟨598504773833371956160621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 798006365111162608214161 598504773833371956160621)
      ·
        refine ⟨224439290187514483560233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 598504773833371956160621 224439290187514483560233)
        ·
          refine ⟨168329467640635862670175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224439290187514483560233 168329467640635862670175)
          ·
            refine ⟨252494201460953794005263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168329467640635862670175 252494201460953794005263)
            ·
              refine ⟨378741302191430691007895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252494201460953794005263 378741302191430691007895)
              ·
                refine ⟨568111953287146036511843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378741302191430691007895 568111953287146036511843)
                ·
                  refine ⟨852167929930719054767765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 568111953287146036511843 852167929930719054767765)
                  ·
                    refine ⟨39945371715502455692239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 852167929930719054767765 39945371715502455692239)
                    ·
                      rfl

theorem cell22_116690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_116690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116690 prefixEnd_116690 := by exact prefixLift 116690
  have htrace : WordTrace (prefixWord ++ tailWord_116690) baseStart_116690 baseEnd_116690 := by
    simpa [prefixWord, tailWord_116690, baseEnd_116690] using wordTrace_append hprefix tailTrace_116690
  have hstable : (prefixWord ++ tailWord_116690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116690).length < 2 ^ (prefixWord ++ tailWord_116690).sum := by decide
  have hdescent : baseEnd_116690 < baseStart_116690 := by decide
  rcases family_descends (prefixWord ++ tailWord_116690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116694 : List Nat := [5, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_116694 : Nat := 118140960795 + 116694 * 2 ^ 59
def prefixEnd_116694 : Nat := 4983230072969 + 3 ^ 40 * 116694 * 2
def baseEnd_116694 : Nat := 13315580332415926197409

theorem tailTrace_116694 : CollatzResearch.WordTrace tailWord_116694 prefixEnd_116694 13315580332415926197409 := by
  unfold tailWord_116694
  simp only [CollatzResearch.WordTrace]
  refine ⟨266011239952815162101321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2837453226163361729080757 266011239952815162101321)
  ·
    refine ⟨199508429964611371575991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266011239952815162101321 199508429964611371575991)
    ·
      refine ⟨299262644946917057363987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199508429964611371575991 299262644946917057363987)
      ·
        refine ⟨448893967420375586045981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299262644946917057363987 448893967420375586045981)
        ·
          refine ⟨168335237782640844767243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448893967420375586045981 168335237782640844767243)
          ·
            refine ⟨252502856673961267150865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168335237782640844767243 252502856673961267150865)
            ·
              refine ⟨189377142505470950363149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252502856673961267150865 189377142505470950363149)
              ·
                refine ⟨71016428439551606386181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189377142505470950363149 71016428439551606386181)
                ·
                  refine ⟨13315580332415926197409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71016428439551606386181 13315580332415926197409)
                  ·
                    rfl

theorem cell22_116694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_116694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116694 prefixEnd_116694 := by exact prefixLift 116694
  have htrace : WordTrace (prefixWord ++ tailWord_116694) baseStart_116694 baseEnd_116694 := by
    simpa [prefixWord, tailWord_116694, baseEnd_116694] using wordTrace_append hprefix tailTrace_116694
  have hstable : (prefixWord ++ tailWord_116694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116694).length < 2 ^ (prefixWord ++ tailWord_116694).sum := by decide
  have hdescent : baseEnd_116694 < baseStart_116694 := by decide
  rcases family_descends (prefixWord ++ tailWord_116694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116733 : List Nat := [1, 4, 1, 1, 1, 2, 2, 5, 5]
def baseStart_116733 : Nat := 118140960795 + 116733 * 2 ^ 59
def prefixEnd_116733 : Nat := 4983230072969 + 3 ^ 40 * 116733 * 2
def baseEnd_116733 : Nat := 13320030498088225622369

theorem tailTrace_116733 : CollatzResearch.WordTrace tailWord_116733 prefixEnd_116733 13320030498088225622369 := by
  unfold tailWord_116733
  simp only [CollatzResearch.WordTrace]
  refine ⟨4257602286103752254290853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2838401524069168169527235 4257602286103752254290853)
  ·
    refine ⟨798300428644453547679535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4257602286103752254290853 798300428644453547679535)
    ·
      refine ⟨1197450642966680321519303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 798300428644453547679535 1197450642966680321519303)
      ·
        refine ⟨1796175964450020482278955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1197450642966680321519303 1796175964450020482278955)
        ·
          refine ⟨2694263946675030723418433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1796175964450020482278955 2694263946675030723418433)
          ·
            refine ⟨2020697960006273042563825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2694263946675030723418433 2020697960006273042563825)
            ·
              refine ⟨1515523470004704781922869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2020697960006273042563825 1515523470004704781922869)
              ·
                refine ⟨142080325312941073305269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1515523470004704781922869 142080325312941073305269)
                ·
                  refine ⟨13320030498088225622369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142080325312941073305269 13320030498088225622369)
                  ·
                    rfl

theorem cell22_116733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_116733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116733 prefixEnd_116733 := by exact prefixLift 116733
  have htrace : WordTrace (prefixWord ++ tailWord_116733) baseStart_116733 baseEnd_116733 := by
    simpa [prefixWord, tailWord_116733, baseEnd_116733] using wordTrace_append hprefix tailTrace_116733
  have hstable : (prefixWord ++ tailWord_116733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116733).length < 2 ^ (prefixWord ++ tailWord_116733).sum := by decide
  have hdescent : baseEnd_116733 < baseStart_116733 := by decide
  rcases family_descends (prefixWord ++ tailWord_116733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116829 : List Nat := [1, 4, 4, 1, 1, 2, 1, 4, 4]
def baseStart_116829 : Nat := 118140960795 + 116829 * 2 ^ 59
def prefixEnd_116829 : Nat := 4983230072969 + 3 ^ 40 * 116829 * 2
def baseEnd_116829 : Nat := 13330984752050808822271

theorem tailTrace_116829 : CollatzResearch.WordTrace tailWord_116829 prefixEnd_116829 13330984752050808822271 := by
  unfold tailWord_116829
  simp only [CollatzResearch.WordTrace]
  refine ⟨4261103693755960649785541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2840735795837307099857027 4261103693755960649785541)
  ·
    refine ⟨798956942579242621834789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4261103693755960649785541 798956942579242621834789)
    ·
      refine ⟨149804426733607991594023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 798956942579242621834789 149804426733607991594023)
      ·
        refine ⟨224706640100411987391035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149804426733607991594023 224706640100411987391035)
        ·
          refine ⟨337059960150617981086553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224706640100411987391035 337059960150617981086553)
          ·
            refine ⟨252794970112963485814915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337059960150617981086553 252794970112963485814915)
            ·
              refine ⟨379192455169445228722373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252794970112963485814915 379192455169445228722373)
              ·
                refine ⟨71098585344270980385445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 379192455169445228722373 71098585344270980385445)
                ·
                  refine ⟨13330984752050808822271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71098585344270980385445 13330984752050808822271)
                  ·
                    rfl

theorem cell22_116829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_116829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116829 prefixEnd_116829 := by exact prefixLift 116829
  have htrace : WordTrace (prefixWord ++ tailWord_116829) baseStart_116829 baseEnd_116829 := by
    simpa [prefixWord, tailWord_116829, baseEnd_116829] using wordTrace_append hprefix tailTrace_116829
  have hstable : (prefixWord ++ tailWord_116829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116829).length < 2 ^ (prefixWord ++ tailWord_116829).sum := by decide
  have hdescent : baseEnd_116829 < baseStart_116829 := by decide
  rcases family_descends (prefixWord ++ tailWord_116829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116855 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 5, 3]
def baseStart_116855 : Nat := 118140960795 + 116855 * 2 ^ 59
def prefixEnd_116855 : Nat := 4983230072969 + 3 ^ 40 * 116855 * 2
def baseEnd_116855 : Nat := 40001854587497025316733

theorem tailTrace_116855 : CollatzResearch.WordTrace tailWord_116855 prefixEnd_116855 40001854587497025316733 := by
  unfold tailWord_116855
  simp only [CollatzResearch.WordTrace]
  refine ⟨4262051991661767090232019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2841367994441178060154679 4262051991661767090232019)
  ·
    refine ⟨6393077987492650635348029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4262051991661767090232019 6393077987492650635348029)
    ·
      refine ⟨2397404245309743988255511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6393077987492650635348029 2397404245309743988255511)
      ·
        refine ⟨3596106367964615982383267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2397404245309743988255511 3596106367964615982383267)
        ·
          refine ⟨5394159551946923973574901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3596106367964615982383267 5394159551946923973574901)
          ·
            refine ⟨505702457995024122522647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5394159551946923973574901 505702457995024122522647)
            ·
              refine ⟨758553686992536183783971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505702457995024122522647 758553686992536183783971)
              ·
                refine ⟨1137830530488804275675957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758553686992536183783971 1137830530488804275675957)
                ·
                  refine ⟨106671612233325400844621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1137830530488804275675957 106671612233325400844621)
                  ·
                    refine ⟨40001854587497025316733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106671612233325400844621 40001854587497025316733)
                    ·
                      rfl

theorem cell22_116855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_116855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116855 prefixEnd_116855 := by exact prefixLift 116855
  have htrace : WordTrace (prefixWord ++ tailWord_116855) baseStart_116855 baseEnd_116855 := by
    simpa [prefixWord, tailWord_116855, baseEnd_116855] using wordTrace_append hprefix tailTrace_116855
  have hstable : (prefixWord ++ tailWord_116855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116855).length < 2 ^ (prefixWord ++ tailWord_116855).sum := by decide
  have hdescent : baseEnd_116855 < baseStart_116855 := by decide
  rcases family_descends (prefixWord ++ tailWord_116855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116960 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 4, 4]
def baseStart_116960 : Nat := 118140960795 + 116960 * 2 ^ 59
def prefixEnd_116960 : Nat := 4983230072969 + 3 ^ 40 * 116960 * 2
def baseEnd_116960 : Nat := 40037798233311751441411

theorem tailTrace_116960 : CollatzResearch.WordTrace tailWord_116960 prefixEnd_116960 40037798233311751441411 := by
  unfold tailWord_116960
  simp only [CollatzResearch.WordTrace]
  refine ⟨2132940828140685011402167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2843921104187580015202889 2132940828140685011402167)
  ·
    refine ⟨3199411242211027517103251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2132940828140685011402167 3199411242211027517103251)
    ·
      refine ⟨4799116863316541275654877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3199411242211027517103251 4799116863316541275654877)
      ·
        refine ⟨1799668823743702978370579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4799116863316541275654877 1799668823743702978370579)
        ·
          refine ⟨2699503235615554467555869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1799668823743702978370579 2699503235615554467555869)
          ·
            refine ⟨1012313713355832925333451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2699503235615554467555869 1012313713355832925333451)
            ·
              refine ⟨1518470570033749388000177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1012313713355832925333451 1518470570033749388000177)
              ·
                refine ⟨1138852927525312041000133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1518470570033749388000177 1138852927525312041000133)
                ·
                  refine ⟨213534923910996007687525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1138852927525312041000133 213534923910996007687525)
                  ·
                    refine ⟨40037798233311751441411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 213534923910996007687525 40037798233311751441411)
                    ·
                      rfl

theorem cell22_116960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_116960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116960 prefixEnd_116960 := by exact prefixLift 116960
  have htrace : WordTrace (prefixWord ++ tailWord_116960) baseStart_116960 baseEnd_116960 := by
    simpa [prefixWord, tailWord_116960, baseEnd_116960] using wordTrace_append hprefix tailTrace_116960
  have hstable : (prefixWord ++ tailWord_116960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116960).length < 2 ^ (prefixWord ++ tailWord_116960).sum := by decide
  have hdescent : baseEnd_116960 < baseStart_116960 := by decide
  rcases family_descends (prefixWord ++ tailWord_116960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116975 : List Nat := [1, 1, 2, 1, 6, 1, 2, 8]
def baseStart_116975 : Nat := 118140960795 + 116975 * 2 ^ 59
def prefixEnd_116975 : Nat := 4983230072969 + 3 ^ 40 * 116975 * 2
def baseEnd_116975 : Nat := 4449214782206301368485

theorem tailTrace_116975 : CollatzResearch.WordTrace tailWord_116975 prefixEnd_116975 4449214782206301368485 := by
  unfold tailWord_116975
  simp only [CollatzResearch.WordTrace]
  refine ⟨4266428751227027584600379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2844285834151351723066919 4266428751227027584600379)
  ·
    refine ⟨6399643126840541376900569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4266428751227027584600379 6399643126840541376900569)
    ·
      refine ⟨4799732345130406032675427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6399643126840541376900569 4799732345130406032675427)
      ·
        refine ⟨7199598517695609049013141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4799732345130406032675427 7199598517695609049013141)
        ·
          refine ⟨337481180516981674172491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7199598517695609049013141 337481180516981674172491)
          ·
            refine ⟨506221770775472511258737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337481180516981674172491 506221770775472511258737)
            ·
              refine ⟨379666328081604383444053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506221770775472511258737 379666328081604383444053)
              ·
                refine ⟨4449214782206301368485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 379666328081604383444053 4449214782206301368485)
                ·
                  rfl

theorem cell22_116975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 8].length) (baseStart_116975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116975 prefixEnd_116975 := by exact prefixLift 116975
  have htrace : WordTrace (prefixWord ++ tailWord_116975) baseStart_116975 baseEnd_116975 := by
    simpa [prefixWord, tailWord_116975, baseEnd_116975] using wordTrace_append hprefix tailTrace_116975
  have hstable : (prefixWord ++ tailWord_116975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116975).length < 2 ^ (prefixWord ++ tailWord_116975).sum := by decide
  have hdescent : baseEnd_116975 < baseStart_116975 := by decide
  rcases family_descends (prefixWord ++ tailWord_116975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116994 : List Nat := [3, 4, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_116994 : Nat := 118140960795 + 116994 * 2 ^ 59
def prefixEnd_116994 : Nat := 4983230072969 + 3 ^ 40 * 116994 * 2
def baseEnd_116994 : Nat := 40049437128146996091307

theorem tailTrace_116994 : CollatzResearch.WordTrace tailWord_116994 prefixEnd_116994 40049437128146996091307 := by
  unfold tailWord_116994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1066780434539548457385509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2844747825438795886361357 1066780434539548457385509)
  ·
    refine ⟨200021331476165335759783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1066780434539548457385509 200021331476165335759783)
    ·
      refine ⟨300031997214248003639675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200021331476165335759783 300031997214248003639675)
      ·
        refine ⟨450047995821372005459513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300031997214248003639675 450047995821372005459513)
        ·
          refine ⟨337535996866029004094635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450047995821372005459513 337535996866029004094635)
          ·
            refine ⟨506303995299043506141953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337535996866029004094635 506303995299043506141953)
            ·
              refine ⟨379727996474282629606465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506303995299043506141953 379727996474282629606465)
              ·
                refine ⟨284795997355711972204849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379727996474282629606465 284795997355711972204849)
                ·
                  refine ⟨213596998016783979153637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284795997355711972204849 213596998016783979153637)
                  ·
                    refine ⟨40049437128146996091307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 213596998016783979153637 40049437128146996091307)
                    ·
                      rfl

theorem cell22_116994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_116994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116994 prefixEnd_116994 := by exact prefixLift 116994
  have htrace : WordTrace (prefixWord ++ tailWord_116994) baseStart_116994 baseEnd_116994 := by
    simpa [prefixWord, tailWord_116994, baseEnd_116994] using wordTrace_append hprefix tailTrace_116994
  have hstable : (prefixWord ++ tailWord_116994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116994).length < 2 ^ (prefixWord ++ tailWord_116994).sum := by decide
  have hdescent : baseEnd_116994 < baseStart_116994 := by decide
  rcases family_descends (prefixWord ++ tailWord_116994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116996 : List Nat := [2, 3, 2, 2, 3, 1, 2, 2, 2, 3]
def baseStart_116996 : Nat := 118140960795 + 116996 * 2 ^ 59
def prefixEnd_116996 : Nat := 4983230072969 + 3 ^ 40 * 116996 * 2
def baseEnd_116996 : Nat := 40050121769019657541301

theorem tailTrace_116996 : CollatzResearch.WordTrace tailWord_116996 prefixEnd_116996 40050121769019657541301 := by
  unfold tailWord_116996
  simp only [CollatzResearch.WordTrace]
  refine ⟨2133597342075474085557421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2844796456100632114076561 2133597342075474085557421)
  ·
    refine ⟨800099003278302782084033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2133597342075474085557421 800099003278302782084033)
    ·
      refine ⟨600074252458727086563025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 800099003278302782084033 600074252458727086563025)
      ·
        refine ⟨450055689344045314922269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600074252458727086563025 450055689344045314922269)
        ·
          refine ⟨168770883504016993095851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 450055689344045314922269 168770883504016993095851)
          ·
            refine ⟨253156325256025489643777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168770883504016993095851 253156325256025489643777)
            ·
              refine ⟨189867243942019117232833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253156325256025489643777 189867243942019117232833)
              ·
                refine ⟨142400432956514337924625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189867243942019117232833 142400432956514337924625)
                ·
                  refine ⟨106800324717385753443469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142400432956514337924625 106800324717385753443469)
                  ·
                    refine ⟨40050121769019657541301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106800324717385753443469 40050121769019657541301)
                    ·
                      rfl

theorem cell22_116996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_116996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_116996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_116996 prefixEnd_116996 := by exact prefixLift 116996
  have htrace : WordTrace (prefixWord ++ tailWord_116996) baseStart_116996 baseEnd_116996 := by
    simpa [prefixWord, tailWord_116996, baseEnd_116996] using wordTrace_append hprefix tailTrace_116996
  have hstable : (prefixWord ++ tailWord_116996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116996).length < 2 ^ (prefixWord ++ tailWord_116996).sum := by decide
  have hdescent : baseEnd_116996 < baseStart_116996 := by decide
  rcases family_descends (prefixWord ++ tailWord_116996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117020 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 9]
def baseStart_117020 : Nat := 118140960795 + 117020 * 2 ^ 59
def prefixEnd_117020 : Nat := 4983230072969 + 3 ^ 40 * 117020 * 2
def baseEnd_117020 : Nat := 13352779153163864980409

theorem tailTrace_117020 : CollatzResearch.WordTrace tailWord_117020 prefixEnd_117020 13352779153163864980409 := by
  unfold tailWord_117020
  simp only [CollatzResearch.WordTrace]
  refine ⟨2134035018032000134994257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2845380024042666846659009 2134035018032000134994257)
  ·
    refine ⟨1600526263524000101245693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2134035018032000134994257 1600526263524000101245693)
    ·
      refine ⟨600197348821500037967135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1600526263524000101245693 600197348821500037967135)
      ·
        refine ⟨900296023232250056950703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600197348821500037967135 900296023232250056950703)
        ·
          refine ⟨1350444034848375085426055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900296023232250056950703 1350444034848375085426055)
          ·
            refine ⟨2025666052272562628139083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350444034848375085426055 2025666052272562628139083)
            ·
              refine ⟨3038499078408843942208625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2025666052272562628139083 3038499078408843942208625)
              ·
                refine ⟨2278874308806632956656469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3038499078408843942208625 2278874308806632956656469)
                ·
                  refine ⟨13352779153163864980409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2278874308806632956656469 13352779153163864980409)
                  ·
                    rfl

theorem cell22_117020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_117020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117020 prefixEnd_117020 := by exact prefixLift 117020
  have htrace : WordTrace (prefixWord ++ tailWord_117020) baseStart_117020 baseEnd_117020 := by
    simpa [prefixWord, tailWord_117020, baseEnd_117020] using wordTrace_append hprefix tailTrace_117020
  have hstable : (prefixWord ++ tailWord_117020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117020).length < 2 ^ (prefixWord ++ tailWord_117020).sum := by decide
  have hdescent : baseEnd_117020 < baseStart_117020 := by decide
  rcases family_descends (prefixWord ++ tailWord_117020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117024 : List Nat := [2, 1, 1, 5, 2, 2, 1, 2, 3, 3]
def baseStart_117024 : Nat := 118140960795 + 117024 * 2 ^ 59
def prefixEnd_117024 : Nat := 4983230072969 + 3 ^ 40 * 117024 * 2
def baseEnd_117024 : Nat := 40059706741236917841215

theorem tailTrace_117024 : CollatzResearch.WordTrace tailWord_117024 prefixEnd_117024 40059706741236917841215 := by
  unfold tailWord_117024
  simp only [CollatzResearch.WordTrace]
  refine ⟨2134107964024754476567063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2845477285366339302089417 2134107964024754476567063)
  ·
    refine ⟨3201161946037131714850595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2134107964024754476567063 3201161946037131714850595)
    ·
      refine ⟨4801742919055697572275893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3201161946037131714850595 4801742919055697572275893)
      ·
        refine ⟨450163398661471647400865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4801742919055697572275893 450163398661471647400865)
        ·
          refine ⟨337622548996103735550649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450163398661471647400865 337622548996103735550649)
          ·
            refine ⟨253216911747077801662987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337622548996103735550649 253216911747077801662987)
            ·
              refine ⟨379825367620616702494481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253216911747077801662987 379825367620616702494481)
              ·
                refine ⟨284869025715462526870861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379825367620616702494481 284869025715462526870861)
                ·
                  refine ⟨106825884643298447576573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284869025715462526870861 106825884643298447576573)
                  ·
                    refine ⟨40059706741236917841215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106825884643298447576573 40059706741236917841215)
                    ·
                      rfl

theorem cell22_117024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 3, 3].length) (baseStart_117024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117024 prefixEnd_117024 := by exact prefixLift 117024
  have htrace : WordTrace (prefixWord ++ tailWord_117024) baseStart_117024 baseEnd_117024 := by
    simpa [prefixWord, tailWord_117024, baseEnd_117024] using wordTrace_append hprefix tailTrace_117024
  have hstable : (prefixWord ++ tailWord_117024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117024).length < 2 ^ (prefixWord ++ tailWord_117024).sum := by decide
  have hdescent : baseEnd_117024 < baseStart_117024 := by decide
  rcases family_descends (prefixWord ++ tailWord_117024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117054 : List Nat := [4, 2, 1, 2, 1, 2, 3, 2, 5]
def baseStart_117054 : Nat := 118140960795 + 117054 * 2 ^ 59
def prefixEnd_117054 : Nat := 4983230072969 + 3 ^ 40 * 117054 * 2
def baseEnd_117054 : Nat := 13356658784775613197041

theorem tailTrace_117054 : CollatzResearch.WordTrace tailWord_117054 prefixEnd_117054 13356658784775613197041 := by
  unfold tailWord_117054
  simp only [CollatzResearch.WordTrace]
  refine ⟨533663764742603009590777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2846206745293882717817477 533663764742603009590777)
  ·
    refine ⟨400247823556952257193083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 533663764742603009590777 400247823556952257193083)
    ·
      refine ⟨600371735335428385789625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400247823556952257193083 600371735335428385789625)
      ·
        refine ⟨450278801501571289342219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600371735335428385789625 450278801501571289342219)
        ·
          refine ⟨675418202252356934013329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450278801501571289342219 675418202252356934013329)
          ·
            refine ⟨506563651689267700509997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 675418202252356934013329 506563651689267700509997)
            ·
              refine ⟨189961369383475387691249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506563651689267700509997 189961369383475387691249)
              ·
                refine ⟨142471027037606540768437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189961369383475387691249 142471027037606540768437)
                ·
                  refine ⟨13356658784775613197041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142471027037606540768437 13356658784775613197041)
                  ·
                    rfl

theorem cell22_117054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_117054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117054 prefixEnd_117054 := by exact prefixLift 117054
  have htrace : WordTrace (prefixWord ++ tailWord_117054) baseStart_117054 baseEnd_117054 := by
    simpa [prefixWord, tailWord_117054, baseEnd_117054] using wordTrace_append hprefix tailTrace_117054
  have hstable : (prefixWord ++ tailWord_117054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117054).length < 2 ^ (prefixWord ++ tailWord_117054).sum := by decide
  have hdescent : baseEnd_117054 < baseStart_117054 := by decide
  rcases family_descends (prefixWord ++ tailWord_117054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117097 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 6, 3]
def baseStart_117097 : Nat := 118140960795 + 117097 * 2 ^ 59
def prefixEnd_117097 : Nat := 4983230072969 + 3 ^ 40 * 117097 * 2
def baseEnd_117097 : Nat := 40084696133089060765991

theorem tailTrace_117097 : CollatzResearch.WordTrace tailWord_117097 prefixEnd_117097 40084696133089060765991 := by
  unfold tailWord_117097
  simp only [CollatzResearch.WordTrace]
  refine ⟨4270878456785042420541545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2847252304523361613694363 4270878456785042420541545)
  ·
    refine ⟨3203158842588781815406159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4270878456785042420541545 3203158842588781815406159)
    ·
      refine ⟨4804738263883172723109239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3203158842588781815406159 4804738263883172723109239)
      ·
        refine ⟨7207107395824759084663859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4804738263883172723109239 7207107395824759084663859)
        ·
          refine ⟨10810661093737138626995789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7207107395824759084663859 10810661093737138626995789)
          ·
            refine ⟨4053997910151426985123421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10810661093737138626995789 4053997910151426985123421)
            ·
              refine ⟨1520249216306785119421283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4053997910151426985123421 1520249216306785119421283)
              ·
                refine ⟨2280373824460177679131925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520249216306785119421283 2280373824460177679131925)
                ·
                  refine ⟨106892523021570828709309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2280373824460177679131925 106892523021570828709309)
                  ·
                    refine ⟨40084696133089060765991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106892523021570828709309 40084696133089060765991)
                    ·
                      rfl

theorem cell22_117097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 3].length) (baseStart_117097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117097 prefixEnd_117097 := by exact prefixLift 117097
  have htrace : WordTrace (prefixWord ++ tailWord_117097) baseStart_117097 baseEnd_117097 := by
    simpa [prefixWord, tailWord_117097, baseEnd_117097] using wordTrace_append hprefix tailTrace_117097
  have hstable : (prefixWord ++ tailWord_117097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117097).length < 2 ^ (prefixWord ++ tailWord_117097).sum := by decide
  have hdescent : baseEnd_117097 < baseStart_117097 := by decide
  rcases family_descends (prefixWord ++ tailWord_117097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117127 : List Nat := [1, 1, 4, 2, 2, 1, 4, 7]
def baseStart_117127 : Nat := 118140960795 + 117127 * 2 ^ 59
def prefixEnd_117127 : Nat := 4983230072969 + 3 ^ 40 * 117127 * 2
def baseEnd_117127 : Nat := 4454996194019886946211

theorem tailTrace_117127 : CollatzResearch.WordTrace tailWord_117127 prefixEnd_117127 4454996194019886946211 := by
  unfold tailWord_117127
  simp only [CollatzResearch.WordTrace]
  refine ⟨4271972646676357544133635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2847981764450905029422423 4271972646676357544133635)
  ·
    refine ⟨6407958970014536316200453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4271972646676357544133635 6407958970014536316200453)
    ·
      refine ⟨1201492306877725559287585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6407958970014536316200453 1201492306877725559287585)
      ·
        refine ⟨901119230158294169465689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1201492306877725559287585 901119230158294169465689)
        ·
          refine ⟨675839422618720627099267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 901119230158294169465689 675839422618720627099267)
          ·
            refine ⟨1013759133928080940648901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675839422618720627099267 1013759133928080940648901)
            ·
              refine ⟨190079837611515176371669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1013759133928080940648901 190079837611515176371669)
              ·
                refine ⟨4454996194019886946211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 190079837611515176371669 4454996194019886946211)
                ·
                  rfl

theorem cell22_117127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 7].length) (baseStart_117127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117127 prefixEnd_117127 := by exact prefixLift 117127
  have htrace : WordTrace (prefixWord ++ tailWord_117127) baseStart_117127 baseEnd_117127 := by
    simpa [prefixWord, tailWord_117127, baseEnd_117127] using wordTrace_append hprefix tailTrace_117127
  have hstable : (prefixWord ++ tailWord_117127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117127).length < 2 ^ (prefixWord ++ tailWord_117127).sum := by decide
  have hdescent : baseEnd_117127 < baseStart_117127 := by decide
  rcases family_descends (prefixWord ++ tailWord_117127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117131 : List Nat := [1, 1, 1, 1, 4, 4, 4, 1, 2, 3]
def baseStart_117131 : Nat := 118140960795 + 117131 * 2 ^ 59
def prefixEnd_117131 : Nat := 4983230072969 + 3 ^ 40 * 117131 * 2
def baseEnd_117131 : Nat := 40096335027924305415887

theorem tailTrace_117131 : CollatzResearch.WordTrace tailWord_117131 prefixEnd_117131 40096335027924305415887 := by
  unfold tailWord_117131
  simp only [CollatzResearch.WordTrace]
  refine ⟨4272118538661866227279247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2848079025774577484852831 4272118538661866227279247)
  ·
    refine ⟨6408177807992799340918871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4272118538661866227279247 6408177807992799340918871)
    ·
      refine ⟨9612266711989199011378307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6408177807992799340918871 9612266711989199011378307)
      ·
        refine ⟨14418400067983798517067461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9612266711989199011378307 14418400067983798517067461)
        ·
          refine ⟨2703450012746962221950149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14418400067983798517067461 2703450012746962221950149)
          ·
            refine ⟨506896877390055416615653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2703450012746962221950149 506896877390055416615653)
            ·
              refine ⟨95043164510635390615435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 506896877390055416615653 95043164510635390615435)
              ·
                refine ⟨142564746765953085923153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95043164510635390615435 142564746765953085923153)
                ·
                  refine ⟨106923560074464814442365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142564746765953085923153 106923560074464814442365)
                  ·
                    refine ⟨40096335027924305415887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106923560074464814442365 40096335027924305415887)
                    ·
                      rfl

theorem cell22_117131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 2, 3].length) (baseStart_117131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117131 prefixEnd_117131 := by exact prefixLift 117131
  have htrace : WordTrace (prefixWord ++ tailWord_117131) baseStart_117131 baseEnd_117131 := by
    simpa [prefixWord, tailWord_117131, baseEnd_117131] using wordTrace_append hprefix tailTrace_117131
  have hstable : (prefixWord ++ tailWord_117131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117131).length < 2 ^ (prefixWord ++ tailWord_117131).sum := by decide
  have hdescent : baseEnd_117131 < baseStart_117131 := by decide
  rcases family_descends (prefixWord ++ tailWord_117131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117217 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 8]
def baseStart_117217 : Nat := 118140960795 + 117217 * 2 ^ 59
def prefixEnd_117217 : Nat := 4983230072969 + 3 ^ 40 * 117217 * 2
def baseEnd_117217 : Nat := 13375258195149582588541

theorem tailTrace_117217 : CollatzResearch.WordTrace tailWord_117217 prefixEnd_117217 13375258195149582588541 := by
  unfold tailWord_117217
  simp only [CollatzResearch.WordTrace]
  refine ⟨4275255216350302914909905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2850170144233535276606603 4275255216350302914909905)
  ·
    refine ⟨3206441412262727186182429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4275255216350302914909905 3206441412262727186182429)
    ·
      refine ⟨1202415529598522694818411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3206441412262727186182429 1202415529598522694818411)
      ·
        refine ⟨1803623294397784042227617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1202415529598522694818411 1803623294397784042227617)
        ·
          refine ⟨1352717470798338031670713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1803623294397784042227617 1352717470798338031670713)
          ·
            refine ⟨1014538103098753523753035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1352717470798338031670713 1014538103098753523753035)
            ·
              refine ⟨1521807154648130285629553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014538103098753523753035 1521807154648130285629553)
              ·
                refine ⟨1141355365986097714222165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1521807154648130285629553 1141355365986097714222165)
                ·
                  refine ⟨13375258195149582588541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1141355365986097714222165 13375258195149582588541)
                  ·
                    rfl

theorem cell22_117217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 8].length) (baseStart_117217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117217 prefixEnd_117217 := by exact prefixLift 117217
  have htrace : WordTrace (prefixWord ++ tailWord_117217) baseStart_117217 baseEnd_117217 := by
    simpa [prefixWord, tailWord_117217, baseEnd_117217] using wordTrace_append hprefix tailTrace_117217
  have hstable : (prefixWord ++ tailWord_117217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117217).length < 2 ^ (prefixWord ++ tailWord_117217).sum := by decide
  have hdescent : baseEnd_117217 < baseStart_117217 := by decide
  rcases family_descends (prefixWord ++ tailWord_117217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117247 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 3, 6]
def baseStart_117247 : Nat := 118140960795 + 117247 * 2 ^ 59
def prefixEnd_117247 : Nat := 4983230072969 + 3 ^ 40 * 117247 * 2
def baseEnd_117247 : Nat := 40136044198538669515531

theorem tailTrace_117247 : CollatzResearch.WordTrace tailWord_117247 prefixEnd_117247 40136044198538669515531 := by
  unfold tailWord_117247
  simp only [CollatzResearch.WordTrace]
  refine ⟨4276349406241618038501995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2850899604161078692334663 4276349406241618038501995)
  ·
    refine ⟨6414524109362427057752993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4276349406241618038501995 6414524109362427057752993)
    ·
      refine ⟨4810893082021820293314745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6414524109362427057752993 4810893082021820293314745)
      ·
        refine ⟨3608169811516365219986059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4810893082021820293314745 3608169811516365219986059)
        ·
          refine ⟨5412254717274547829979089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3608169811516365219986059 5412254717274547829979089)
          ·
            refine ⟨4059191037955910872484317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5412254717274547829979089 4059191037955910872484317)
            ·
              refine ⟨1522196639233466577181619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4059191037955910872484317 1522196639233466577181619)
              ·
                refine ⟨2283294958850199865772429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1522196639233466577181619 2283294958850199865772429)
                ·
                  refine ⟨856235609568824949664661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2283294958850199865772429 856235609568824949664661)
                  ·
                    refine ⟨40136044198538669515531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 856235609568824949664661 40136044198538669515531)
                    ·
                      rfl

theorem cell22_117247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_117247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117247 prefixEnd_117247 := by exact prefixLift 117247
  have htrace : WordTrace (prefixWord ++ tailWord_117247) baseStart_117247 baseEnd_117247 := by
    simpa [prefixWord, tailWord_117247, baseEnd_117247] using wordTrace_append hprefix tailTrace_117247
  have hstable : (prefixWord ++ tailWord_117247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117247).length < 2 ^ (prefixWord ++ tailWord_117247).sum := by decide
  have hdescent : baseEnd_117247 < baseStart_117247 := by decide
  rcases family_descends (prefixWord ++ tailWord_117247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117345 : List Nat := [1, 2, 3, 1, 1, 4, 4, 2, 1, 3]
def baseStart_117345 : Nat := 118140960795 + 117345 * 2 ^ 59
def prefixEnd_117345 : Nat := 4983230072969 + 3 ^ 40 * 117345 * 2
def baseEnd_117345 : Nat := 40169591601299080565231

theorem tailTrace_117345 : CollatzResearch.WordTrace tailWord_117345 prefixEnd_117345 40169591601299080565231 := by
  unfold tailWord_117345
  simp only [CollatzResearch.WordTrace]
  refine ⟨4279923759886580775569489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2853282506591053850379659 4279923759886580775569489)
  ·
    refine ⟨3209942819914935581677117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4279923759886580775569489 3209942819914935581677117)
    ·
      refine ⟨1203728557468100843128919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3209942819914935581677117 1203728557468100843128919)
      ·
        refine ⟨1805592836202151264693379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1203728557468100843128919 1805592836202151264693379)
        ·
          refine ⟨2708389254303226897040069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1805592836202151264693379 2708389254303226897040069)
          ·
            refine ⟨507822985181855043195013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2708389254303226897040069 507822985181855043195013)
            ·
              refine ⟨95216809721597820599065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 507822985181855043195013 95216809721597820599065)
              ·
                refine ⟨71412607291198365449299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95216809721597820599065 71412607291198365449299)
                ·
                  refine ⟨107118910936797548173949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71412607291198365449299 107118910936797548173949)
                  ·
                    refine ⟨40169591601299080565231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107118910936797548173949 40169591601299080565231)
                    ·
                      rfl

theorem cell22_117345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_117345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117345 prefixEnd_117345 := by exact prefixLift 117345
  have htrace : WordTrace (prefixWord ++ tailWord_117345) baseStart_117345 baseEnd_117345 := by
    simpa [prefixWord, tailWord_117345, baseEnd_117345] using wordTrace_append hprefix tailTrace_117345
  have hstable : (prefixWord ++ tailWord_117345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117345).length < 2 ^ (prefixWord ++ tailWord_117345).sum := by decide
  have hdescent : baseEnd_117345 < baseStart_117345 := by decide
  rcases family_descends (prefixWord ++ tailWord_117345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117369 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 8]
def baseStart_117369 : Nat := 118140960795 + 117369 * 2 ^ 59
def prefixEnd_117369 : Nat := 4983230072969 + 3 ^ 40 * 117369 * 2
def baseEnd_117369 : Nat := 13392602430590339321719

theorem tailTrace_117369 : CollatzResearch.WordTrace tailWord_117369 prefixEnd_117369 13392602430590339321719 := by
  unfold tailWord_117369
  simp only [CollatzResearch.WordTrace]
  refine ⟨4280799111799632874443161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2853866074533088582962107 4280799111799632874443161)
  ·
    refine ⟨3210599333849724655832371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4280799111799632874443161 3210599333849724655832371)
    ·
      refine ⟨4815899000774586983748557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3210599333849724655832371 4815899000774586983748557)
      ·
        refine ⟨1805962125290470118905709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4815899000774586983748557 1805962125290470118905709)
        ·
          refine ⟨677235796983926294589641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1805962125290470118905709 677235796983926294589641)
          ·
            refine ⟨507926847737944720942231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 677235796983926294589641 507926847737944720942231)
            ·
              refine ⟨761890271606917081413347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507926847737944720942231 761890271606917081413347)
              ·
                refine ⟨1142835407410375622120021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761890271606917081413347 1142835407410375622120021)
                ·
                  refine ⟨13392602430590339321719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1142835407410375622120021 13392602430590339321719)
                  ·
                    rfl

theorem cell22_117369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 8].length) (baseStart_117369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117369 prefixEnd_117369 := by exact prefixLift 117369
  have htrace : WordTrace (prefixWord ++ tailWord_117369) baseStart_117369 baseEnd_117369 := by
    simpa [prefixWord, tailWord_117369, baseEnd_117369] using wordTrace_append hprefix tailTrace_117369
  have hstable : (prefixWord ++ tailWord_117369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117369).length < 2 ^ (prefixWord ++ tailWord_117369).sum := by decide
  have hdescent : baseEnd_117369 < baseStart_117369 := by decide
  rcases family_descends (prefixWord ++ tailWord_117369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117401 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 4, 3]
def baseStart_117401 : Nat := 118140960795 + 117401 * 2 ^ 59
def prefixEnd_117401 : Nat := 4983230072969 + 3 ^ 40 * 117401 * 2
def baseEnd_117401 : Nat := 40188761545733601165059

theorem tailTrace_117401 : CollatzResearch.WordTrace tailWord_117401 prefixEnd_117401 40188761545733601165059 := by
  unfold tailWord_117401
  simp only [CollatzResearch.WordTrace]
  refine ⟨4281966247683702339608057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2854644165122468226405371 4281966247683702339608057)
  ·
    refine ⟨3211474685762776754706043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4281966247683702339608057 3211474685762776754706043)
    ·
      refine ⟨4817212028644165132059065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3211474685762776754706043 4817212028644165132059065)
      ·
        refine ⟨3612909021483123849044299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4817212028644165132059065 3612909021483123849044299)
        ·
          refine ⟨5419363532224685773566449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3612909021483123849044299 5419363532224685773566449)
          ·
            refine ⟨4064522649168514330174837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5419363532224685773566449 4064522649168514330174837)
            ·
              refine ⟨381048998359548218453891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4064522649168514330174837 381048998359548218453891)
              ·
                refine ⟨571573497539322327680837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381048998359548218453891 571573497539322327680837)
                ·
                  refine ⟨107170030788622936440157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 571573497539322327680837 107170030788622936440157)
                  ·
                    refine ⟨40188761545733601165059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107170030788622936440157 40188761545733601165059)
                    ·
                      rfl

theorem cell22_117401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 3].length) (baseStart_117401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117401 prefixEnd_117401 := by exact prefixLift 117401
  have htrace : WordTrace (prefixWord ++ tailWord_117401) baseStart_117401 baseEnd_117401 := by
    simpa [prefixWord, tailWord_117401, baseEnd_117401] using wordTrace_append hprefix tailTrace_117401
  have hstable : (prefixWord ++ tailWord_117401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117401).length < 2 ^ (prefixWord ++ tailWord_117401).sum := by decide
  have hdescent : baseEnd_117401 < baseStart_117401 := by decide
  rcases family_descends (prefixWord ++ tailWord_117401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117431 : List Nat := [1, 1, 3, 1, 6, 1, 1, 8]
def baseStart_117431 : Nat := 118140960795 + 117431 * 2 ^ 59
def prefixEnd_117431 : Nat := 4983230072969 + 3 ^ 40 * 117431 * 2
def baseEnd_117431 : Nat := 4466559017647058101663

theorem tailTrace_117431 : CollatzResearch.WordTrace tailWord_117431 prefixEnd_117431 4466559017647058101663 := by
  unfold tailWord_117431
  simp only [CollatzResearch.WordTrace]
  refine ⟨4283060437575017463200147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2855373625050011642133431 4283060437575017463200147)
  ·
    refine ⟨6424590656362526194800221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4283060437575017463200147 6424590656362526194800221)
    ·
      refine ⟨2409221496135947323050083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6424590656362526194800221 2409221496135947323050083)
      ·
        refine ⟨3613832244203920984575125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2409221496135947323050083 3613832244203920984575125)
        ·
          refine ⟨169398386447058796151959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3613832244203920984575125 169398386447058796151959)
          ·
            refine ⟨254097579670588194227939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169398386447058796151959 254097579670588194227939)
            ·
              refine ⟨381146369505882291341909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254097579670588194227939 381146369505882291341909)
              ·
                refine ⟨4466559017647058101663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 381146369505882291341909 4466559017647058101663)
                ·
                  rfl

theorem cell22_117431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 8].length) (baseStart_117431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117431 prefixEnd_117431 := by exact prefixLift 117431
  have htrace : WordTrace (prefixWord ++ tailWord_117431) baseStart_117431 baseEnd_117431 := by
    simpa [prefixWord, tailWord_117431, baseEnd_117431] using wordTrace_append hprefix tailTrace_117431
  have hstable : (prefixWord ++ tailWord_117431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117431).length < 2 ^ (prefixWord ++ tailWord_117431).sum := by decide
  have hdescent : baseEnd_117431 < baseStart_117431 := by decide
  rcases family_descends (prefixWord ++ tailWord_117431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117463 : List Nat := [1, 1, 3, 2, 1, 4, 3, 1, 3, 3]
def baseStart_117463 : Nat := 118140960795 + 117463 * 2 ^ 59
def prefixEnd_117463 : Nat := 4983230072969 + 3 ^ 40 * 117463 * 2
def baseEnd_117463 : Nat := 40209985412786106114869

theorem tailTrace_117463 : CollatzResearch.WordTrace tailWord_117463 prefixEnd_117463 40209985412786106114869 := by
  unfold tailWord_117463
  simp only [CollatzResearch.WordTrace]
  refine ⟨4284227573459086928365043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2856151715639391285576695 4284227573459086928365043)
  ·
    refine ⟨6426341360188630392547565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4284227573459086928365043 6426341360188630392547565)
    ·
      refine ⟨2409878010070736397205337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6426341360188630392547565 2409878010070736397205337)
      ·
        refine ⟨1807408507553052297904003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2409878010070736397205337 1807408507553052297904003)
        ·
          refine ⟨2711112761329578446856005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807408507553052297904003 2711112761329578446856005)
          ·
            refine ⟨508333642749295958785501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2711112761329578446856005 508333642749295958785501)
            ·
              refine ⟨190625116030985984544563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 508333642749295958785501 190625116030985984544563)
              ·
                refine ⟨285937674046478976816845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190625116030985984544563 285937674046478976816845)
                ·
                  refine ⟨107226627767429616306317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285937674046478976816845 107226627767429616306317)
                  ·
                    refine ⟨40209985412786106114869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107226627767429616306317 40209985412786106114869)
                    ·
                      rfl

theorem cell22_117463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_117463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117463 prefixEnd_117463 := by exact prefixLift 117463
  have htrace : WordTrace (prefixWord ++ tailWord_117463) baseStart_117463 baseEnd_117463 := by
    simpa [prefixWord, tailWord_117463, baseEnd_117463] using wordTrace_append hprefix tailTrace_117463
  have hstable : (prefixWord ++ tailWord_117463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117463).length < 2 ^ (prefixWord ++ tailWord_117463).sum := by decide
  have hdescent : baseEnd_117463 < baseStart_117463 := by decide
  rcases family_descends (prefixWord ++ tailWord_117463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117538 : List Nat := [3, 3, 1, 1, 2, 3, 1, 2, 6]
def baseStart_117538 : Nat := 118140960795 + 117538 * 2 ^ 59
def prefixEnd_117538 : Nat := 4983230072969 + 3 ^ 40 * 117538 * 2
def baseEnd_117538 : Nat := 13411886481836970163213

theorem tailTrace_117538 : CollatzResearch.WordTrace tailWord_117538 prefixEnd_117538 13411886481836970163213 := by
  unfold tailWord_117538
  simp only [CollatzResearch.WordTrace]
  refine ⟨1071740762046843684336317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2857975365458249824896845 1071740762046843684336317)
  ·
    refine ⟨401902785767566381626119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1071740762046843684336317 401902785767566381626119)
    ·
      refine ⟨602854178651349572439179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401902785767566381626119 602854178651349572439179)
      ·
        refine ⟨904281267977024358658769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602854178651349572439179 904281267977024358658769)
        ·
          refine ⟨678210950982768268994077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 904281267977024358658769 678210950982768268994077)
          ·
            refine ⟨254329106618538100872779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 678210950982768268994077 254329106618538100872779)
            ·
              refine ⟨381493659927807151309169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254329106618538100872779 381493659927807151309169)
              ·
                refine ⟨286120244945855363481877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381493659927807151309169 286120244945855363481877)
                ·
                  refine ⟨13411886481836970163213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 286120244945855363481877 13411886481836970163213)
                  ·
                    rfl

theorem cell22_117538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_117538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117538 prefixEnd_117538 := by exact prefixLift 117538
  have htrace : WordTrace (prefixWord ++ tailWord_117538) baseStart_117538 baseEnd_117538 := by
    simpa [prefixWord, tailWord_117538, baseEnd_117538] using wordTrace_append hprefix tailTrace_117538
  have hstable : (prefixWord ++ tailWord_117538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117538).length < 2 ^ (prefixWord ++ tailWord_117538).sum := by decide
  have hdescent : baseEnd_117538 < baseStart_117538 := by decide
  rcases family_descends (prefixWord ++ tailWord_117538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117553 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 4, 3]
def baseStart_117553 : Nat := 118140960795 + 117553 * 2 ^ 59
def prefixEnd_117553 : Nat := 4983230072969 + 3 ^ 40 * 117553 * 2
def baseEnd_117553 : Nat := 40240794252055871364593

theorem tailTrace_117553 : CollatzResearch.WordTrace tailWord_117553 prefixEnd_117553 40240794252055871364593 := by
  unfold tailWord_117553
  simp only [CollatzResearch.WordTrace]
  refine ⟨4287510143133032299141313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2858340095422021532760875 4287510143133032299141313)
  ·
    refine ⟨3215632607349774224355985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4287510143133032299141313 3215632607349774224355985)
    ·
      refine ⟨2411724455512330668266989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3215632607349774224355985 2411724455512330668266989)
      ·
        refine ⟨904396670817124000600121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2411724455512330668266989 904396670817124000600121)
        ·
          refine ⟨678297503112843000450091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 904396670817124000600121 678297503112843000450091)
          ·
            refine ⟨1017446254669264500675137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678297503112843000450091 1017446254669264500675137)
            ·
              refine ⟨763084691001948375506353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017446254669264500675137 763084691001948375506353)
              ·
                refine ⟨572313518251461281629765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 763084691001948375506353 572313518251461281629765)
                ·
                  refine ⟨107308784672148990305581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 572313518251461281629765 107308784672148990305581)
                  ·
                    refine ⟨40240794252055871364593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107308784672148990305581 40240794252055871364593)
                    ·
                      rfl

theorem cell22_117553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_117553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117553 prefixEnd_117553 := by exact prefixLift 117553
  have htrace : WordTrace (prefixWord ++ tailWord_117553) baseStart_117553 baseEnd_117553 := by
    simpa [prefixWord, tailWord_117553, baseEnd_117553] using wordTrace_append hprefix tailTrace_117553
  have hstable : (prefixWord ++ tailWord_117553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117553).length < 2 ^ (prefixWord ++ tailWord_117553).sum := by decide
  have hdescent : baseEnd_117553 < baseStart_117553 := by decide
  rcases family_descends (prefixWord ++ tailWord_117553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117555 : List Nat := [1, 1, 1, 2, 6, 2, 2, 3, 4]
def baseStart_117555 : Nat := 118140960795 + 117555 * 2 ^ 59
def prefixEnd_117555 : Nat := 4983230072969 + 3 ^ 40 * 117555 * 2
def baseEnd_117555 : Nat := 13413826297642844271529

theorem tailTrace_117555 : CollatzResearch.WordTrace tailWord_117555 prefixEnd_117555 13413826297642844271529 := by
  unfold tailWord_117555
  simp only [CollatzResearch.WordTrace]
  refine ⟨4287583089125786640714119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2858388726083857760476079 4287583089125786640714119)
  ·
    refine ⟨6431374633688679961071179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4287583089125786640714119 6431374633688679961071179)
    ·
      refine ⟨9647061950533019941606769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6431374633688679961071179 9647061950533019941606769)
      ·
        refine ⟨7235296462899764956205077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9647061950533019941606769 7235296462899764956205077)
        ·
          refine ⟨339154521698426482322113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7235296462899764956205077 339154521698426482322113)
          ·
            refine ⟨254365891273819861741585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339154521698426482322113 254365891273819861741585)
            ·
              refine ⟨190774418455364896306189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254365891273819861741585 190774418455364896306189)
              ·
                refine ⟨71540406920761836114821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190774418455364896306189 71540406920761836114821)
                ·
                  refine ⟨13413826297642844271529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71540406920761836114821 13413826297642844271529)
                  ·
                    rfl

theorem cell22_117555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 4].length) (baseStart_117555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117555 prefixEnd_117555 := by exact prefixLift 117555
  have htrace : WordTrace (prefixWord ++ tailWord_117555) baseStart_117555 baseEnd_117555 := by
    simpa [prefixWord, tailWord_117555, baseEnd_117555] using wordTrace_append hprefix tailTrace_117555
  have hstable : (prefixWord ++ tailWord_117555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117555).length < 2 ^ (prefixWord ++ tailWord_117555).sum := by decide
  have hdescent : baseEnd_117555 < baseStart_117555 := by decide
  rcases family_descends (prefixWord ++ tailWord_117555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117557 : List Nat := [1, 3, 3, 1, 3, 3, 2, 1, 1, 4]
def baseStart_117557 : Nat := 118140960795 + 117557 * 2 ^ 59
def prefixEnd_117557 : Nat := 4983230072969 + 3 ^ 40 * 117557 * 2
def baseEnd_117557 : Nat := 40242163533801194264581

theorem tailTrace_117557 : CollatzResearch.WordTrace tailWord_117557 prefixEnd_117557 40242163533801194264581 := by
  unfold tailWord_117557
  simp only [CollatzResearch.WordTrace]
  refine ⟨4287656035118540982286925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2858437356745693988191283 4287656035118540982286925)
  ·
    refine ⟨1607871013169452868357597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4287656035118540982286925 1607871013169452868357597)
    ·
      refine ⟨602951629938544825634099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1607871013169452868357597 602951629938544825634099)
      ·
        refine ⟨904427444907817238451149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602951629938544825634099 904427444907817238451149)
        ·
          refine ⟨339160291840431464419181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 904427444907817238451149 339160291840431464419181)
          ·
            refine ⟨127185109440161799157193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339160291840431464419181 127185109440161799157193)
            ·
              refine ⟨95388832080121349367895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127185109440161799157193 95388832080121349367895)
              ·
                refine ⟨143083248120182024051843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95388832080121349367895 143083248120182024051843)
                ·
                  refine ⟨214624872180273036077765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143083248120182024051843 214624872180273036077765)
                  ·
                    refine ⟨40242163533801194264581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 214624872180273036077765 40242163533801194264581)
                    ·
                      rfl

theorem cell22_117557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_117557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117557 prefixEnd_117557 := by exact prefixLift 117557
  have htrace : WordTrace (prefixWord ++ tailWord_117557) baseStart_117557 baseEnd_117557 := by
    simpa [prefixWord, tailWord_117557, baseEnd_117557] using wordTrace_append hprefix tailTrace_117557
  have hstable : (prefixWord ++ tailWord_117557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117557).length < 2 ^ (prefixWord ++ tailWord_117557).sum := by decide
  have hdescent : baseEnd_117557 < baseStart_117557 := by decide
  rcases family_descends (prefixWord ++ tailWord_117557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117572 : List Nat := [2, 3, 4, 2, 1, 1, 2, 1, 6]
def baseStart_117572 : Nat := 118140960795 + 117572 * 2 ^ 59
def prefixEnd_117572 : Nat := 4983230072969 + 3 ^ 40 * 117572 * 2
def baseEnd_117572 : Nat := 13415766113448718379845

theorem tailTrace_117572 : CollatzResearch.WordTrace tailWord_117572 prefixEnd_117572 13415766113448718379845 := by
  unfold tailWord_117572
  simp only [CollatzResearch.WordTrace]
  refine ⟨2144101565032099272041485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2858802086709465696055313 2144101565032099272041485)
  ·
    refine ⟨804038086887037227015557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2144101565032099272041485 804038086887037227015557)
    ·
      refine ⟨150757141291319480065417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 804038086887037227015557 150757141291319480065417)
      ·
        refine ⟨113067855968489610049063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150757141291319480065417 113067855968489610049063)
        ·
          refine ⟨169601783952734415073595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113067855968489610049063 169601783952734415073595)
          ·
            refine ⟨254402675929101622610393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169601783952734415073595 254402675929101622610393)
            ·
              refine ⟨190802006946826216957795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254402675929101622610393 190802006946826216957795)
              ·
                refine ⟨286203010420239325436693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190802006946826216957795 286203010420239325436693)
                ·
                  refine ⟨13415766113448718379845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 286203010420239325436693 13415766113448718379845)
                  ·
                    rfl

theorem cell22_117572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_117572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117572 prefixEnd_117572 := by exact prefixLift 117572
  have htrace : WordTrace (prefixWord ++ tailWord_117572) baseStart_117572 baseEnd_117572 := by
    simpa [prefixWord, tailWord_117572, baseEnd_117572] using wordTrace_append hprefix tailTrace_117572
  have hstable : (prefixWord ++ tailWord_117572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117572).length < 2 ^ (prefixWord ++ tailWord_117572).sum := by decide
  have hdescent : baseEnd_117572 < baseStart_117572 := by decide
  rcases family_descends (prefixWord ++ tailWord_117572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117611 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 7]
def baseStart_117611 : Nat := 118140960795 + 117611 * 2 ^ 59
def prefixEnd_117611 : Nat := 4983230072969 + 3 ^ 40 * 117611 * 2
def baseEnd_117611 : Nat := 13420216279121017804805

theorem tailTrace_117611 : CollatzResearch.WordTrace tailWord_117611 prefixEnd_117611 13420216279121017804805 := by
  unfold tailWord_117611
  simp only [CollatzResearch.WordTrace]
  refine ⟨4289625576922908204752687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2859750384615272136501791 4289625576922908204752687)
  ·
    refine ⟨6434438365384362307129031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4289625576922908204752687 6434438365384362307129031)
    ·
      refine ⟨9651657548076543460693547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6434438365384362307129031 9651657548076543460693547)
      ·
        refine ⟨14477486322114815191040321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9651657548076543460693547 14477486322114815191040321)
        ·
          refine ⟨10858114741586111393280241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14477486322114815191040321 10858114741586111393280241)
          ·
            refine ⟨8143586056189583544960181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10858114741586111393280241 8143586056189583544960181)
            ·
              refine ⟨763461192767773457340017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8143586056189583544960181 763461192767773457340017)
              ·
                refine ⟨572595894575830093005013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 763461192767773457340017 572595894575830093005013)
                ·
                  refine ⟨13420216279121017804805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 572595894575830093005013 13420216279121017804805)
                  ·
                    rfl

theorem cell22_117611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 7].length) (baseStart_117611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117611 prefixEnd_117611 := by exact prefixLift 117611
  have htrace : WordTrace (prefixWord ++ tailWord_117611) baseStart_117611 baseEnd_117611 := by
    simpa [prefixWord, tailWord_117611, baseEnd_117611] using wordTrace_append hprefix tailTrace_117611
  have hstable : (prefixWord ++ tailWord_117611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117611).length < 2 ^ (prefixWord ++ tailWord_117611).sum := by decide
  have hdescent : baseEnd_117611 < baseStart_117611 := by decide
  rcases family_descends (prefixWord ++ tailWord_117611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117690 : List Nat := [3, 1, 1, 1, 2, 1, 5, 4, 4]
def baseStart_117690 : Nat := 118140960795 + 117690 * 2 ^ 59
def prefixEnd_117690 : Nat := 4983230072969 + 3 ^ 40 * 117690 * 2
def baseEnd_117690 : Nat := 13429230717277726896391

theorem tailTrace_117690 : CollatzResearch.WordTrace tailWord_117690 prefixEnd_117690 13429230717277726896391 := by
  unfold tailWord_117690
  simp only [CollatzResearch.WordTrace]
  refine ⟨1073126735909176174219631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2861671295757803131252349 1073126735909176174219631)
  ·
    refine ⟨1609690103863764261329447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1073126735909176174219631 1609690103863764261329447)
    ·
      refine ⟨2414535155795646391994171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1609690103863764261329447 2414535155795646391994171)
      ·
        refine ⟨3621802733693469587991257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2414535155795646391994171 3621802733693469587991257)
        ·
          refine ⟨2716352050270102190993443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3621802733693469587991257 2716352050270102190993443)
          ·
            refine ⟨4074528075405153286490165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2716352050270102190993443 4074528075405153286490165)
            ·
              refine ⟨381987007069233120608453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4074528075405153286490165 381987007069233120608453)
              ·
                refine ⟨71622563825481210114085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 381987007069233120608453 71622563825481210114085)
                ·
                  refine ⟨13429230717277726896391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71622563825481210114085 13429230717277726896391)
                  ·
                    rfl

theorem cell22_117690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_117690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117690 prefixEnd_117690 := by exact prefixLift 117690
  have htrace : WordTrace (prefixWord ++ tailWord_117690) baseStart_117690 baseEnd_117690 := by
    simpa [prefixWord, tailWord_117690, baseEnd_117690] using wordTrace_append hprefix tailTrace_117690
  have hstable : (prefixWord ++ tailWord_117690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117690).length < 2 ^ (prefixWord ++ tailWord_117690).sum := by decide
  have hdescent : baseEnd_117690 < baseStart_117690 := by decide
  rcases family_descends (prefixWord ++ tailWord_117690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117703 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 4, 4]
def baseStart_117703 : Nat := 118140960795 + 117703 * 2 ^ 59
def prefixEnd_117703 : Nat := 4983230072969 + 3 ^ 40 * 117703 * 2
def baseEnd_117703 : Nat := 40292142317505480114133

theorem tailTrace_117703 : CollatzResearch.WordTrace tailWord_117703 prefixEnd_117703 40292142317505480114133 := by
  unfold tailWord_117703
  simp only [CollatzResearch.WordTrace]
  refine ⟨4292981092589607917101763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2861987395059738611401175 4292981092589607917101763)
  ·
    refine ⟨6439471638884411875652645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4292981092589607917101763 6439471638884411875652645)
    ·
      refine ⟨1207400932290827226684871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6439471638884411875652645 1207400932290827226684871)
      ·
        refine ⟨1811101398436240840027307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1207400932290827226684871 1811101398436240840027307)
        ·
          refine ⟨2716652097654361260040961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1811101398436240840027307 2716652097654361260040961)
          ·
            refine ⟨2037489073240770945030721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2716652097654361260040961 2037489073240770945030721)
            ·
              refine ⟨1528116804930578208773041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2037489073240770945030721 1528116804930578208773041)
              ·
                refine ⟨1146087603697933656579781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1528116804930578208773041 1146087603697933656579781)
                ·
                  refine ⟨214891425693362560608709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1146087603697933656579781 214891425693362560608709)
                  ·
                    refine ⟨40292142317505480114133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 214891425693362560608709 40292142317505480114133)
                    ·
                      rfl

theorem cell22_117703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_117703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117703 prefixEnd_117703 := by exact prefixLift 117703
  have htrace : WordTrace (prefixWord ++ tailWord_117703) baseStart_117703 baseEnd_117703 := by
    simpa [prefixWord, tailWord_117703, baseEnd_117703] using wordTrace_append hprefix tailTrace_117703
  have hstable : (prefixWord ++ tailWord_117703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117703).length < 2 ^ (prefixWord ++ tailWord_117703).sum := by decide
  have hdescent : baseEnd_117703 < baseStart_117703 := by decide
  rcases family_descends (prefixWord ++ tailWord_117703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117720 : List Nat := [2, 1, 2, 2, 2, 3, 3, 1, 2, 4]
def baseStart_117720 : Nat := 118140960795 + 117720 * 2 ^ 59
def prefixEnd_117720 : Nat := 4983230072969 + 3 ^ 40 * 117720 * 2
def baseEnd_117720 : Nat := 40297961764923102439081

theorem tailTrace_117720 : CollatzResearch.WordTrace tailWord_117720 prefixEnd_117720 40297961764923102439081 := by
  unfold tailWord_117720
  simp only [CollatzResearch.WordTrace]
  refine ⟨2146800566764009910235307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2862400755685346546980409 2146800566764009910235307)
  ·
    refine ⟨3220200850146014865352961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2146800566764009910235307 3220200850146014865352961)
    ·
      refine ⟨2415150637609511149014721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3220200850146014865352961 2415150637609511149014721)
      ·
        refine ⟨1811362978207133361761041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2415150637609511149014721 1811362978207133361761041)
        ·
          refine ⟨1358522233655350021320781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1811362978207133361761041 1358522233655350021320781)
          ·
            refine ⟨509445837620756257995293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1358522233655350021320781 509445837620756257995293)
            ·
              refine ⟨191042189107783596748235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 509445837620756257995293 191042189107783596748235)
              ·
                refine ⟨286563283661675395122353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191042189107783596748235 286563283661675395122353)
                ·
                  refine ⟨214922462746256546341765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286563283661675395122353 214922462746256546341765)
                  ·
                    refine ⟨40297961764923102439081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 214922462746256546341765 40297961764923102439081)
                    ·
                      rfl

theorem cell22_117720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_117720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117720 prefixEnd_117720 := by exact prefixLift 117720
  have htrace : WordTrace (prefixWord ++ tailWord_117720) baseStart_117720 baseEnd_117720 := by
    simpa [prefixWord, tailWord_117720, baseEnd_117720] using wordTrace_append hprefix tailTrace_117720
  have hstable : (prefixWord ++ tailWord_117720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117720).length < 2 ^ (prefixWord ++ tailWord_117720).sum := by decide
  have hdescent : baseEnd_117720 < baseStart_117720 := by decide
  rcases family_descends (prefixWord ++ tailWord_117720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117784 : List Nat := [2, 1, 2, 3, 2, 2, 3, 3, 1, 3]
def baseStart_117784 : Nat := 118140960795 + 117784 * 2 ^ 59
def prefixEnd_117784 : Nat := 4983230072969 + 3 ^ 40 * 117784 * 2
def baseEnd_117784 : Nat := 40319870272848268838885

theorem tailTrace_117784 : CollatzResearch.WordTrace tailWord_117784 prefixEnd_117784 40319870272848268838885 := by
  unfold tailWord_117784
  simp only [CollatzResearch.WordTrace]
  refine ⟨2147967702648079375400203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2863956936864105833866937 2147967702648079375400203)
  ·
    refine ⟨3221951553972119063100305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2147967702648079375400203 3221951553972119063100305)
    ·
      refine ⟨2416463665479089297325229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3221951553972119063100305 2416463665479089297325229)
      ·
        refine ⟨906173874554658486496961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2416463665479089297325229 906173874554658486496961)
        ·
          refine ⟨679630405915993864872721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906173874554658486496961 679630405915993864872721)
          ·
            refine ⟨509722804436995398654541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 679630405915993864872721 509722804436995398654541)
            ·
              refine ⟨191146051663873274495453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 509722804436995398654541 191146051663873274495453)
              ·
                refine ⟨71679769373952477935795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191146051663873274495453 71679769373952477935795)
                ·
                  refine ⟨107519654060928716903693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71679769373952477935795 107519654060928716903693)
                  ·
                    refine ⟨40319870272848268838885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107519654060928716903693 40319870272848268838885)
                    ·
                      rfl

theorem cell22_117784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 1, 3].length) (baseStart_117784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117784 prefixEnd_117784 := by exact prefixLift 117784
  have htrace : WordTrace (prefixWord ++ tailWord_117784) baseStart_117784 baseEnd_117784 := by
    simpa [prefixWord, tailWord_117784, baseEnd_117784] using wordTrace_append hprefix tailTrace_117784
  have hstable : (prefixWord ++ tailWord_117784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117784).length < 2 ^ (prefixWord ++ tailWord_117784).sum := by decide
  have hdescent : baseEnd_117784 < baseStart_117784 := by decide
  rcases family_descends (prefixWord ++ tailWord_117784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117810 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_117810 : Nat := 118140960795 + 117810 * 2 ^ 59
def prefixEnd_117810 : Nat := 4983230072969 + 3 ^ 40 * 117810 * 2
def baseEnd_117810 : Nat := 40328770604192867688805

theorem tailTrace_117810 : CollatzResearch.WordTrace tailWord_117810 prefixEnd_117810 40328770604192867688805 := by
  unfold tailWord_117810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1074220925800491297811721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2864589135467976794164589 1074220925800491297811721)
  ·
    refine ⟨805665694350368473358791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1074220925800491297811721 805665694350368473358791)
    ·
      refine ⟨1208498541525552710038187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 805665694350368473358791 1208498541525552710038187)
      ·
        refine ⟨1812747812288329065057281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1208498541525552710038187 1812747812288329065057281)
        ·
          refine ⟨1359560859216246798792961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1812747812288329065057281 1359560859216246798792961)
          ·
            refine ⟨1019670644412185099094721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1359560859216246798792961 1019670644412185099094721)
            ·
              refine ⟨764752983309138824321041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1019670644412185099094721 764752983309138824321041)
              ·
                refine ⟨573564737481854118240781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764752983309138824321041 573564737481854118240781)
                ·
                  refine ⟨215086776555695294340293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 573564737481854118240781 215086776555695294340293)
                  ·
                    refine ⟨40328770604192867688805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 215086776555695294340293 40328770604192867688805)
                    ·
                      rfl

theorem cell22_117810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_117810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117810 prefixEnd_117810 := by exact prefixLift 117810
  have htrace : WordTrace (prefixWord ++ tailWord_117810) baseStart_117810 baseEnd_117810 := by
    simpa [prefixWord, tailWord_117810, baseEnd_117810] using wordTrace_append hprefix tailTrace_117810
  have hstable : (prefixWord ++ tailWord_117810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117810).length < 2 ^ (prefixWord ++ tailWord_117810).sum := by decide
  have hdescent : baseEnd_117810 < baseStart_117810 := by decide
  rcases family_descends (prefixWord ++ tailWord_117810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117814 : List Nat := [5, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_117814 : Nat := 118140960795 + 117814 * 2 ^ 59
def prefixEnd_117814 : Nat := 4983230072969 + 3 ^ 40 * 117814 * 2
def baseEnd_117814 : Nat := 13443379961979396862931

theorem tailTrace_117814 : CollatzResearch.WordTrace tailWord_117814 prefixEnd_117814 13443379961979396862931 := by
  unfold tailWord_117814
  simp only [CollatzResearch.WordTrace]
  refine ⟨268564349699217117149531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2864686396791649249594997 268564349699217117149531)
  ·
    refine ⟨402846524548825675724297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268564349699217117149531 402846524548825675724297)
    ·
      refine ⟨302134893411619256793223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402846524548825675724297 302134893411619256793223)
      ·
        refine ⟨453202340117428885189835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302134893411619256793223 453202340117428885189835)
        ·
          refine ⟨679803510176143327784753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453202340117428885189835 679803510176143327784753)
          ·
            refine ⟨509852632632107495838565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 679803510176143327784753 509852632632107495838565)
            ·
              refine ⟨95597368618520155469731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 509852632632107495838565 95597368618520155469731)
              ·
                refine ⟨143396052927780233204597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95597368618520155469731 143396052927780233204597)
                ·
                  refine ⟨13443379961979396862931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143396052927780233204597 13443379961979396862931)
                  ·
                    rfl

theorem cell22_117814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_117814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117814 prefixEnd_117814 := by exact prefixLift 117814
  have htrace : WordTrace (prefixWord ++ tailWord_117814) baseStart_117814 baseEnd_117814 := by
    simpa [prefixWord, tailWord_117814, baseEnd_117814] using wordTrace_append hprefix tailTrace_117814
  have hstable : (prefixWord ++ tailWord_117814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117814).length < 2 ^ (prefixWord ++ tailWord_117814).sum := by decide
  have hdescent : baseEnd_117814 < baseStart_117814 := by decide
  rcases family_descends (prefixWord ++ tailWord_117814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117840 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 6, 3]
def baseStart_117840 : Nat := 118140960795 + 117840 * 2 ^ 59
def prefixEnd_117840 : Nat := 4983230072969 + 3 ^ 40 * 117840 * 2
def baseEnd_117840 : Nat := 40339040217282789438713

theorem tailTrace_117840 : CollatzResearch.WordTrace tailWord_117840 prefixEnd_117840 40339040217282789438713 := by
  unfold tailWord_117840
  simp only [CollatzResearch.WordTrace]
  refine ⟨2148988946546640157419487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2865318595395520209892649 2148988946546640157419487)
  ·
    refine ⟨3223483419819960236129231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2148988946546640157419487 3223483419819960236129231)
    ·
      refine ⟨4835225129729940354193847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3223483419819960236129231 4835225129729940354193847)
      ·
        refine ⟨7252837694594910531290771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4835225129729940354193847 7252837694594910531290771)
        ·
          refine ⟨10879256541892365796936157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7252837694594910531290771 10879256541892365796936157)
          ·
            refine ⟨4079721203209637173851059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10879256541892365796936157 4079721203209637173851059)
            ·
              refine ⟨6119581804814455760776589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4079721203209637173851059 6119581804814455760776589)
              ·
                refine ⟨2294843176805420910291221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6119581804814455760776589 2294843176805420910291221)
                ·
                  refine ⟨107570773912754105169901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2294843176805420910291221 107570773912754105169901)
                  ·
                    refine ⟨40339040217282789438713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107570773912754105169901 40339040217282789438713)
                    ·
                      rfl

theorem cell22_117840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 6, 3].length) (baseStart_117840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117840 prefixEnd_117840 := by exact prefixLift 117840
  have htrace : WordTrace (prefixWord ++ tailWord_117840) baseStart_117840 baseEnd_117840 := by
    simpa [prefixWord, tailWord_117840, baseEnd_117840] using wordTrace_append hprefix tailTrace_117840
  have hstable : (prefixWord ++ tailWord_117840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117840).length < 2 ^ (prefixWord ++ tailWord_117840).sum := by decide
  have hdescent : baseEnd_117840 < baseStart_117840 := by decide
  rcases family_descends (prefixWord ++ tailWord_117840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117855 : List Nat := [1, 1, 2, 3, 1, 1, 3, 4, 2, 4]
def baseStart_117855 : Nat := 118140960795 + 117855 * 2 ^ 59
def prefixEnd_117855 : Nat := 4983230072969 + 3 ^ 40 * 117855 * 2
def baseEnd_117855 : Nat := 40344175023827750313667

theorem tailTrace_117855 : CollatzResearch.WordTrace tailWord_117855 prefixEnd_117855 40344175023827750313667 := by
  unfold tailWord_117855
  simp only [CollatzResearch.WordTrace]
  refine ⟨4298524988038937876635019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2865683325359291917756679 4298524988038937876635019)
  ·
    refine ⟨6447787482058406814952529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4298524988038937876635019 6447787482058406814952529)
    ·
      refine ⟨4835840611543805111214397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6447787482058406814952529 4835840611543805111214397)
      ·
        refine ⟨1813440229328926916705399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4835840611543805111214397 1813440229328926916705399)
        ·
          refine ⟨2720160343993390375058099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1813440229328926916705399 2720160343993390375058099)
          ·
            refine ⟨4080240515990085562587149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2720160343993390375058099 4080240515990085562587149)
            ·
              refine ⟨1530090193496282085970181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4080240515990085562587149 1530090193496282085970181)
              ·
                refine ⟨286891911280552891119409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1530090193496282085970181 286891911280552891119409)
                ·
                  refine ⟨215168933460414668339557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286891911280552891119409 215168933460414668339557)
                  ·
                    refine ⟨40344175023827750313667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 215168933460414668339557 40344175023827750313667)
                    ·
                      rfl

theorem cell22_117855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_117855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117855 prefixEnd_117855 := by exact prefixLift 117855
  have htrace : WordTrace (prefixWord ++ tailWord_117855) baseStart_117855 baseEnd_117855 := by
    simpa [prefixWord, tailWord_117855, baseEnd_117855] using wordTrace_append hprefix tailTrace_117855
  have hstable : (prefixWord ++ tailWord_117855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117855).length < 2 ^ (prefixWord ++ tailWord_117855).sum := by decide
  have hdescent : baseEnd_117855 < baseStart_117855 := by decide
  rcases family_descends (prefixWord ++ tailWord_117855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117857 : List Nat := [1, 2, 3, 1, 1, 2, 3, 4, 2, 3]
def baseStart_117857 : Nat := 118140960795 + 117857 * 2 ^ 59
def prefixEnd_117857 : Nat := 4983230072969 + 3 ^ 40 * 117857 * 2
def baseEnd_117857 : Nat := 40344859664700411763661

theorem tailTrace_117857 : CollatzResearch.WordTrace tailWord_117857 prefixEnd_117857 40344859664700411763661 := by
  unfold tailWord_117857
  simp only [CollatzResearch.WordTrace]
  refine ⟨4298597934031692218207825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2865731956021128145471883 4298597934031692218207825)
  ·
    refine ⟨3223948450523769163655869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4298597934031692218207825 3223948450523769163655869)
    ·
      refine ⟨1208980668946413436370951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3223948450523769163655869 1208980668946413436370951)
      ·
        refine ⟨1813471003419620154556427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1208980668946413436370951 1813471003419620154556427)
        ·
          refine ⟨2720206505129430231834641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1813471003419620154556427 2720206505129430231834641)
          ·
            refine ⟨2040154878847072673875981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2720206505129430231834641 2040154878847072673875981)
            ·
              refine ⟨765058079567652252703493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2040154878847072673875981 765058079567652252703493)
              ·
                refine ⟨143448389918934797381905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 765058079567652252703493 143448389918934797381905)
                ·
                  refine ⟨107586292439201098036429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143448389918934797381905 107586292439201098036429)
                  ·
                    refine ⟨40344859664700411763661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107586292439201098036429 40344859664700411763661)
                    ·
                      rfl

theorem cell22_117857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_117857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117857 prefixEnd_117857 := by exact prefixLift 117857
  have htrace : WordTrace (prefixWord ++ tailWord_117857) baseStart_117857 baseEnd_117857 := by
    simpa [prefixWord, tailWord_117857, baseEnd_117857] using wordTrace_append hprefix tailTrace_117857
  have hstable : (prefixWord ++ tailWord_117857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117857).length < 2 ^ (prefixWord ++ tailWord_117857).sum := by decide
  have hdescent : baseEnd_117857 < baseStart_117857 := by decide
  rcases family_descends (prefixWord ++ tailWord_117857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117889 : List Nat := [1, 2, 4, 2, 2, 3, 1, 1, 2, 4]
def baseStart_117889 : Nat := 118140960795 + 117889 * 2 ^ 59
def prefixEnd_117889 : Nat := 4983230072969 + 3 ^ 40 * 117889 * 2
def baseEnd_117889 : Nat := 40355813918662994963563

theorem tailTrace_117889 : CollatzResearch.WordTrace tailWord_117889 prefixEnd_117889 40355813918662994963563 := by
  unfold tailWord_117889
  simp only [CollatzResearch.WordTrace]
  refine ⟨4299765069915761683372721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2866510046610507788915147 4299765069915761683372721)
  ·
    refine ⟨3224823802436821262529541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4299765069915761683372721 3224823802436821262529541)
    ·
      refine ⟨604654462956903986724289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3224823802436821262529541 604654462956903986724289)
      ·
        refine ⟨453490847217677990043217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 604654462956903986724289 453490847217677990043217)
        ·
          refine ⟨340118135413258492532413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453490847217677990043217 340118135413258492532413)
          ·
            refine ⟨127544300779971934699655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340118135413258492532413 127544300779971934699655)
            ·
              refine ⟨191316451169957902049483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127544300779971934699655 191316451169957902049483)
              ·
                refine ⟨286974676754936853074225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191316451169957902049483 286974676754936853074225)
                ·
                  refine ⟨215231007566202639805669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286974676754936853074225 215231007566202639805669)
                  ·
                    refine ⟨40355813918662994963563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 215231007566202639805669 40355813918662994963563)
                    ·
                      rfl

theorem cell22_117889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_117889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117889 prefixEnd_117889 := by exact prefixLift 117889
  have htrace : WordTrace (prefixWord ++ tailWord_117889) baseStart_117889 baseEnd_117889 := by
    simpa [prefixWord, tailWord_117889, baseEnd_117889] using wordTrace_append hprefix tailTrace_117889
  have hstable : (prefixWord ++ tailWord_117889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117889).length < 2 ^ (prefixWord ++ tailWord_117889).sum := by decide
  have hdescent : baseEnd_117889 < baseStart_117889 := by decide
  rcases family_descends (prefixWord ++ tailWord_117889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117953 : List Nat := [1, 2, 6, 1, 1, 1, 3, 3, 1, 3]
def baseStart_117953 : Nat := 118140960795 + 117953 * 2 ^ 59
def prefixEnd_117953 : Nat := 4983230072969 + 3 ^ 40 * 117953 * 2
def baseEnd_117953 : Nat := 40377722426588161363367

theorem tailTrace_117953 : CollatzResearch.WordTrace tailWord_117953 prefixEnd_117953 40377722426588161363367 := by
  unfold tailWord_117953
  simp only [CollatzResearch.WordTrace]
  refine ⟨4302099341683900613702513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2868066227789267075801675 4302099341683900613702513)
  ·
    refine ⟨3226574506262925460276885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4302099341683900613702513 3226574506262925460276885)
    ·
      refine ⟨151245679981074630950479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3226574506262925460276885 151245679981074630950479)
      ·
        refine ⟨226868519971611946425719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151245679981074630950479 226868519971611946425719)
        ·
          refine ⟨340302779957417919638579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226868519971611946425719 340302779957417919638579)
          ·
            refine ⟨510454169936126879457869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340302779957417919638579 510454169936126879457869)
            ·
              refine ⟨191420313726047579796701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510454169936126879457869 191420313726047579796701)
              ·
                refine ⟨71782617647267842423763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191420313726047579796701 71782617647267842423763)
                ·
                  refine ⟨107673926470901763635645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71782617647267842423763 107673926470901763635645)
                  ·
                    refine ⟨40377722426588161363367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107673926470901763635645 40377722426588161363367)
                    ·
                      rfl

theorem cell22_117953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_117953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117953 prefixEnd_117953 := by exact prefixLift 117953
  have htrace : WordTrace (prefixWord ++ tailWord_117953) baseStart_117953 baseEnd_117953 := by
    simpa [prefixWord, tailWord_117953, baseEnd_117953] using wordTrace_append hprefix tailTrace_117953
  have hstable : (prefixWord ++ tailWord_117953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117953).length < 2 ^ (prefixWord ++ tailWord_117953).sum := by decide
  have hdescent : baseEnd_117953 < baseStart_117953 := by decide
  rcases family_descends (prefixWord ++ tailWord_117953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117960 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 8]
def baseStart_117960 : Nat := 118140960795 + 117960 * 2 ^ 59
def prefixEnd_117960 : Nat := 4983230072969 + 3 ^ 40 * 117960 * 2
def baseEnd_117960 : Nat := 13460039556547492146115

theorem tailTrace_117960 : CollatzResearch.WordTrace tailWord_117960 prefixEnd_117960 13460039556547492146115 := by
  unfold tailWord_117960
  simp only [CollatzResearch.WordTrace]
  refine ⟨2151177326329270404603667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2868236435105693872804889 2151177326329270404603667)
  ·
    refine ⟨3226765989493905606905501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2151177326329270404603667 3226765989493905606905501)
    ·
      refine ⟨1210037246060214602589563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3226765989493905606905501 1210037246060214602589563)
      ·
        refine ⟨1815055869090321903884345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1210037246060214602589563 1815055869090321903884345)
        ·
          refine ⟨1361291901817741427913259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1815055869090321903884345 1361291901817741427913259)
          ·
            refine ⟨2041937852726612141869889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361291901817741427913259 2041937852726612141869889)
            ·
              refine ⟨1531453389544959106402417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2041937852726612141869889 1531453389544959106402417)
              ·
                refine ⟨1148590042158719329801813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1531453389544959106402417 1148590042158719329801813)
                ·
                  refine ⟨13460039556547492146115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1148590042158719329801813 13460039556547492146115)
                  ·
                    rfl

theorem cell22_117960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 8].length) (baseStart_117960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117960 prefixEnd_117960 := by exact prefixLift 117960
  have htrace : WordTrace (prefixWord ++ tailWord_117960) baseStart_117960 baseEnd_117960 := by
    simpa [prefixWord, tailWord_117960, baseEnd_117960] using wordTrace_append hprefix tailTrace_117960
  have hstable : (prefixWord ++ tailWord_117960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117960).length < 2 ^ (prefixWord ++ tailWord_117960).sum := by decide
  have hdescent : baseEnd_117960 < baseStart_117960 := by decide
  rcases family_descends (prefixWord ++ tailWord_117960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117992 : List Nat := [2, 1, 4, 1, 2, 1, 2, 3, 1, 5]
def baseStart_117992 : Nat := 118140960795 + 117992 * 2 ^ 59
def prefixEnd_117992 : Nat := 4983230072969 + 3 ^ 40 * 117992 * 2
def baseEnd_117992 : Nat := 40391072923605059638247

theorem tailTrace_117992 : CollatzResearch.WordTrace tailWord_117992 prefixEnd_117992 40391072923605059638247 := by
  unfold tailWord_117992
  simp only [CollatzResearch.WordTrace]
  refine ⟨2151760894271305137186115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2869014525695073516248153 2151760894271305137186115)
  ·
    refine ⟨3227641341406957705779173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2151760894271305137186115 3227641341406957705779173)
    ·
      refine ⟨605182751513804569833595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3227641341406957705779173 605182751513804569833595)
      ·
        refine ⟨907774127270706854750393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605182751513804569833595 907774127270706854750393)
        ·
          refine ⟨680830595453030141062795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 907774127270706854750393 680830595453030141062795)
          ·
            refine ⟨1021245893179545211594193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680830595453030141062795 1021245893179545211594193)
            ·
              refine ⟨765934419884658908695645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1021245893179545211594193 765934419884658908695645)
              ·
                refine ⟨287225407456747090760867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 765934419884658908695645 287225407456747090760867)
                ·
                  refine ⟨430838111185120636141301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287225407456747090760867 430838111185120636141301)
                  ·
                    refine ⟨40391072923605059638247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 430838111185120636141301 40391072923605059638247)
                    ·
                      rfl

theorem cell22_117992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_117992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_117992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_117992 prefixEnd_117992 := by exact prefixLift 117992
  have htrace : WordTrace (prefixWord ++ tailWord_117992) baseStart_117992 baseEnd_117992 := by
    simpa [prefixWord, tailWord_117992, baseEnd_117992] using wordTrace_append hprefix tailTrace_117992
  have hstable : (prefixWord ++ tailWord_117992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117992).length < 2 ^ (prefixWord ++ tailWord_117992).sum := by decide
  have hdescent : baseEnd_117992 < baseStart_117992 := by decide
  rcases family_descends (prefixWord ++ tailWord_117992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118052 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_118052 : Nat := 118140960795 + 118052 * 2 ^ 59
def prefixEnd_118052 : Nat := 4983230072969 + 3 ^ 40 * 118052 * 2
def baseEnd_118052 : Nat := 40411612149784903138063

theorem tailTrace_118052 : CollatzResearch.WordTrace tailWord_118052 prefixEnd_118052 40411612149784903138063 := by
  unfold tailWord_118052
  simp only [CollatzResearch.WordTrace]
  refine ⟨2152855084162620260778205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2870473445550160347704273 2152855084162620260778205)
  ·
    refine ⟨807320656560982597791827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2152855084162620260778205 807320656560982597791827)
    ·
      refine ⟨1210980984841473896687741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 807320656560982597791827 1210980984841473896687741)
      ·
        refine ⟨454117869315552711257903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1210980984841473896687741 454117869315552711257903)
        ·
          refine ⟨681176803973329066886855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454117869315552711257903 681176803973329066886855)
          ·
            refine ⟨1021765205959993600330283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681176803973329066886855 1021765205959993600330283)
            ·
              refine ⟨1532647808939990400495425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021765205959993600330283 1532647808939990400495425)
              ·
                refine ⟨1149485856704992800371569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532647808939990400495425 1149485856704992800371569)
                ·
                  refine ⟨862114392528744600278677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1149485856704992800371569 862114392528744600278677)
                  ·
                    refine ⟨40411612149784903138063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 862114392528744600278677 40411612149784903138063)
                    ·
                      rfl

theorem cell22_118052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_118052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118052 prefixEnd_118052 := by exact prefixLift 118052
  have htrace : WordTrace (prefixWord ++ tailWord_118052) baseStart_118052 baseEnd_118052 := by
    simpa [prefixWord, tailWord_118052, baseEnd_118052] using wordTrace_append hprefix tailTrace_118052
  have hstable : (prefixWord ++ tailWord_118052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118052).length < 2 ^ (prefixWord ++ tailWord_118052).sum := by decide
  have hdescent : baseEnd_118052 < baseStart_118052 := by decide
  rcases family_descends (prefixWord ++ tailWord_118052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118101 : List Nat := [1, 3, 2, 2, 3, 2, 3, 1, 5]
def baseStart_118101 : Nat := 118140960795 + 118101 * 2 ^ 59
def prefixEnd_118101 : Nat := 4983230072969 + 3 ^ 40 * 118101 * 2
def baseEnd_118101 : Nat := 13476128617055036220971

theorem tailTrace_118101 : CollatzResearch.WordTrace tailWord_118101 prefixEnd_118101 13476128617055036220971 := by
  unfold tailWord_118101
  simp only [CollatzResearch.WordTrace]
  refine ⟨4307497345147721890090157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2871664896765147926726771 4307497345147721890090157)
  ·
    refine ⟨1615311504430395708783809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4307497345147721890090157 1615311504430395708783809)
    ·
      refine ⟨1211483628322796781587857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1615311504430395708783809 1211483628322796781587857)
      ·
        refine ⟨908612721242097586190893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1211483628322796781587857 908612721242097586190893)
        ·
          refine ⟨340729770465786594821585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 908612721242097586190893 340729770465786594821585)
          ·
            refine ⟨255547327849339946116189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340729770465786594821585 255547327849339946116189)
            ·
              refine ⟨95830247943502479793571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255547327849339946116189 95830247943502479793571)
              ·
                refine ⟨143745371915253719690357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95830247943502479793571 143745371915253719690357)
                ·
                  refine ⟨13476128617055036220971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143745371915253719690357 13476128617055036220971)
                  ·
                    rfl

theorem cell22_118101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_118101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118101 prefixEnd_118101 := by exact prefixLift 118101
  have htrace : WordTrace (prefixWord ++ tailWord_118101) baseStart_118101 baseEnd_118101 := by
    simpa [prefixWord, tailWord_118101, baseEnd_118101] using wordTrace_append hprefix tailTrace_118101
  have hstable : (prefixWord ++ tailWord_118101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118101).length < 2 ^ (prefixWord ++ tailWord_118101).sum := by decide
  have hdescent : baseEnd_118101 < baseStart_118101 := by decide
  rcases family_descends (prefixWord ++ tailWord_118101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118122 : List Nat := [3, 1, 3, 3, 3, 1, 1, 3, 1, 3]
def baseStart_118122 : Nat := 118140960795 + 118122 * 2 ^ 59
def prefixEnd_118122 : Nat := 4983230072969 + 3 ^ 40 * 118122 * 2
def baseEnd_118122 : Nat := 40435574580328053887849

theorem tailTrace_118122 : CollatzResearch.WordTrace tailWord_118122 prefixEnd_118122 40435574580328053887849 := by
  unfold tailWord_118122
  simp only [CollatzResearch.WordTrace]
  refine ⟨1077065819517910619151155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2872175518714428317736413 1077065819517910619151155)
  ·
    refine ⟨1615598729276865928726733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1077065819517910619151155 1615598729276865928726733)
    ·
      refine ⟨605849523478824723272525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1615598729276865928726733 605849523478824723272525)
      ·
        refine ⟨227193571304559271227197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 605849523478824723272525 227193571304559271227197)
        ·
          refine ⟨85197589239209726710199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227193571304559271227197 85197589239209726710199)
          ·
            refine ⟨127796383858814590065299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85197589239209726710199 127796383858814590065299)
            ·
              refine ⟨191694575788221885097949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127796383858814590065299 191694575788221885097949)
              ·
                refine ⟨71885465920583206911731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191694575788221885097949 71885465920583206911731)
                ·
                  refine ⟨107828198880874810367597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71885465920583206911731 107828198880874810367597)
                  ·
                    refine ⟨40435574580328053887849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107828198880874810367597 40435574580328053887849)
                    ·
                      rfl

theorem cell22_118122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_118122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118122 prefixEnd_118122 := by exact prefixLift 118122
  have htrace : WordTrace (prefixWord ++ tailWord_118122) baseStart_118122 baseEnd_118122 := by
    simpa [prefixWord, tailWord_118122, baseEnd_118122] using wordTrace_append hprefix tailTrace_118122
  have hstable : (prefixWord ++ tailWord_118122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118122).length < 2 ^ (prefixWord ++ tailWord_118122).sum := by decide
  have hdescent : baseEnd_118122 < baseStart_118122 := by decide
  rcases family_descends (prefixWord ++ tailWord_118122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118127 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 3, 5]
def baseStart_118127 : Nat := 118140960795 + 118127 * 2 ^ 59
def prefixEnd_118127 : Nat := 4983230072969 + 3 ^ 40 * 118127 * 2
def baseEnd_118127 : Nat := 40437286182509707512833

theorem tailTrace_118127 : CollatzResearch.WordTrace tailWord_118127 prefixEnd_118127 40437286182509707512833 := by
  unfold tailWord_118127
  simp only [CollatzResearch.WordTrace]
  refine ⟨4308445643053528330536635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2872297095369018887024423 4308445643053528330536635)
  ·
    refine ⟨6462668464580292495804953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4308445643053528330536635 6462668464580292495804953)
    ·
      refine ⟨4847001348435219371853715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6462668464580292495804953 4847001348435219371853715)
      ·
        refine ⟨7270502022652829057780573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4847001348435219371853715 7270502022652829057780573)
        ·
          refine ⟨2726438258494810896667715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7270502022652829057780573 2726438258494810896667715)
          ·
            refine ⟨4089657387742216345001573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2726438258494810896667715 4089657387742216345001573)
            ·
              refine ⟨766810760201665564687795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4089657387742216345001573 766810760201665564687795)
              ·
                refine ⟨1150216140302498347031693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766810760201665564687795 1150216140302498347031693)
                ·
                  refine ⟨431331052613436880136885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1150216140302498347031693 431331052613436880136885)
                  ·
                    refine ⟨40437286182509707512833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 431331052613436880136885 40437286182509707512833)
                    ·
                      rfl

theorem cell22_118127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_118127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118127 prefixEnd_118127 := by exact prefixLift 118127
  have htrace : WordTrace (prefixWord ++ tailWord_118127) baseStart_118127 baseEnd_118127 := by
    simpa [prefixWord, tailWord_118127, baseEnd_118127] using wordTrace_append hprefix tailTrace_118127
  have hstable : (prefixWord ++ tailWord_118127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118127).length < 2 ^ (prefixWord ++ tailWord_118127).sum := by decide
  have hdescent : baseEnd_118127 < baseStart_118127 := by decide
  rcases family_descends (prefixWord ++ tailWord_118127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118206 : List Nat := [4, 2, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_118206 : Nat := 118140960795 + 118206 * 2 ^ 59
def prefixEnd_118206 : Nat := 4983230072969 + 3 ^ 40 * 118206 * 2
def baseEnd_118206 : Nat := 40464329496979834787591

theorem tailTrace_118206 : CollatzResearch.WordTrace tailWord_118206 prefixEnd_118206 40464329496979834787591 := by
  unfold tailWord_118206
  simp only [CollatzResearch.WordTrace]
  refine ⟨538915876220915602832809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2874218006511549881774981 538915876220915602832809)
  ·
    refine ⟨404186907165686702124607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 538915876220915602832809 404186907165686702124607)
    ·
      refine ⟨606280360748530053186911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404186907165686702124607 606280360748530053186911)
      ·
        refine ⟨909420541122795079780367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606280360748530053186911 909420541122795079780367)
        ·
          refine ⟨1364130811684192619670551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909420541122795079780367 1364130811684192619670551)
          ·
            refine ⟨2046196217526288929505827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1364130811684192619670551 2046196217526288929505827)
            ·
              refine ⟨3069294326289433394258741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2046196217526288929505827 3069294326289433394258741)
              ·
                refine ⟨287746343089634380711757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3069294326289433394258741 287746343089634380711757)
                ·
                  refine ⟨107904878658612892766909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287746343089634380711757 107904878658612892766909)
                  ·
                    refine ⟨40464329496979834787591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107904878658612892766909 40464329496979834787591)
                    ·
                      rfl

theorem cell22_118206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_118206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118206 prefixEnd_118206 := by exact prefixLift 118206
  have htrace : WordTrace (prefixWord ++ tailWord_118206) baseStart_118206 baseEnd_118206 := by
    simpa [prefixWord, tailWord_118206, baseEnd_118206] using wordTrace_append hprefix tailTrace_118206
  have hstable : (prefixWord ++ tailWord_118206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118206).length < 2 ^ (prefixWord ++ tailWord_118206).sum := by decide
  have hdescent : baseEnd_118206 < baseStart_118206 := by decide
  rcases family_descends (prefixWord ++ tailWord_118206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118219 : List Nat := [1, 1, 1, 1, 3, 3, 4, 3, 5]
def baseStart_118219 : Nat := 118140960795 + 118219 * 2 ^ 59
def prefixEnd_118219 : Nat := 4983230072969 + 3 ^ 40 * 118219 * 2
def baseEnd_118219 : Nat := 13489593220884044737517

theorem tailTrace_118219 : CollatzResearch.WordTrace tailWord_118219 prefixEnd_118219 13489593220884044737517 := by
  unfold tailWord_118219
  simp only [CollatzResearch.WordTrace]
  refine ⟨4311801158720228042885711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2874534105813485361923807 4311801158720228042885711)
  ·
    refine ⟨6467701738080342064328567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4311801158720228042885711 6467701738080342064328567)
    ·
      refine ⟨9701552607120513096492851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6467701738080342064328567 9701552607120513096492851)
      ·
        refine ⟨14552328910680769644739277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9701552607120513096492851 14552328910680769644739277)
        ·
          refine ⟨5457123341505288616777229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14552328910680769644739277 5457123341505288616777229)
          ·
            refine ⟨2046421253064483231291461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5457123341505288616777229 2046421253064483231291461)
            ·
              refine ⟨383703984949590605867149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2046421253064483231291461 383703984949590605867149)
              ·
                refine ⟨143888994356096477200181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383703984949590605867149 143888994356096477200181)
                ·
                  refine ⟨13489593220884044737517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143888994356096477200181 13489593220884044737517)
                  ·
                    rfl

theorem cell22_118219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 5].length) (baseStart_118219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118219 prefixEnd_118219 := by exact prefixLift 118219
  have htrace : WordTrace (prefixWord ++ tailWord_118219) baseStart_118219 baseEnd_118219 := by
    simpa [prefixWord, tailWord_118219, baseEnd_118219] using wordTrace_append hprefix tailTrace_118219
  have hstable : (prefixWord ++ tailWord_118219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118219).length < 2 ^ (prefixWord ++ tailWord_118219).sum := by decide
  have hdescent : baseEnd_118219 < baseStart_118219 := by decide
  rcases family_descends (prefixWord ++ tailWord_118219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118264 : List Nat := [2, 1, 2, 1, 1, 5, 1, 3, 6]
def baseStart_118264 : Nat := 118140960795 + 118264 * 2 ^ 59
def prefixEnd_118264 : Nat := 4983230072969 + 3 ^ 40 * 118264 * 2
def baseEnd_118264 : Nat := 13494728027429005612471

theorem tailTrace_118264 : CollatzResearch.WordTrace tailWord_118264 prefixEnd_118264 13494728027429005612471 := by
  unfold tailWord_118264
  simp only [CollatzResearch.WordTrace]
  refine ⟨2156721221778600364136923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2875628295704800485515897 2156721221778600364136923)
  ·
    refine ⟨3235081832667900546205385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2156721221778600364136923 3235081832667900546205385)
    ·
      refine ⟨2426311374500925409654039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3235081832667900546205385 2426311374500925409654039)
      ·
        refine ⟨3639467061751388114481059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2426311374500925409654039 3639467061751388114481059)
        ·
          refine ⟨5459200592627082171721589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3639467061751388114481059 5459200592627082171721589)
          ·
            refine ⟨511800055558788953598899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5459200592627082171721589 511800055558788953598899)
            ·
              refine ⟨767700083338183430398349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511800055558788953598899 767700083338183430398349)
              ·
                refine ⟨287887531251818786399381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 767700083338183430398349 287887531251818786399381)
                ·
                  refine ⟨13494728027429005612471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 287887531251818786399381 13494728027429005612471)
                  ·
                    rfl

theorem cell22_118264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 6].length) (baseStart_118264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118264 prefixEnd_118264 := by exact prefixLift 118264
  have htrace : WordTrace (prefixWord ++ tailWord_118264) baseStart_118264 baseEnd_118264 := by
    simpa [prefixWord, tailWord_118264, baseEnd_118264] using wordTrace_append hprefix tailTrace_118264
  have hstable : (prefixWord ++ tailWord_118264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118264).length < 2 ^ (prefixWord ++ tailWord_118264).sum := by decide
  have hdescent : baseEnd_118264 < baseStart_118264 := by decide
  rcases family_descends (prefixWord ++ tailWord_118264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118283 : List Nat := [1, 1, 1, 1, 8, 1, 2, 2, 1, 4]
def baseStart_118283 : Nat := 118140960795 + 118283 * 2 ^ 59
def prefixEnd_118283 : Nat := 4983230072969 + 3 ^ 40 * 118283 * 2
def baseEnd_118283 : Nat := 40490688170577300612355

theorem tailTrace_118283 : CollatzResearch.WordTrace tailWord_118283 prefixEnd_118283 40490688170577300612355 := by
  unfold tailWord_118283
  simp only [CollatzResearch.WordTrace]
  refine ⟨4314135430488366973215503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2876090286992244648810335 4314135430488366973215503)
  ·
    refine ⟨6471203145732550459823255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4314135430488366973215503 6471203145732550459823255)
    ·
      refine ⟨9706804718598825689734883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6471203145732550459823255 9706804718598825689734883)
      ·
        refine ⟨14560207077898238534602325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9706804718598825689734883 14560207077898238534602325)
        ·
          refine ⟨170627426694119982827371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 14560207077898238534602325 170627426694119982827371)
          ·
            refine ⟨255941140041179974241057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170627426694119982827371 255941140041179974241057)
            ·
              refine ⟨191955855030884980680793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255941140041179974241057 191955855030884980680793)
              ·
                refine ⟨143966891273163735510595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191955855030884980680793 143966891273163735510595)
                ·
                  refine ⟨215950336909745603265893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143966891273163735510595 215950336909745603265893)
                  ·
                    refine ⟨40490688170577300612355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 215950336909745603265893 40490688170577300612355)
                    ·
                      rfl

theorem cell22_118283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 4].length) (baseStart_118283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118283 prefixEnd_118283 := by exact prefixLift 118283
  have htrace : WordTrace (prefixWord ++ tailWord_118283) baseStart_118283 baseEnd_118283 := by
    simpa [prefixWord, tailWord_118283, baseEnd_118283] using wordTrace_append hprefix tailTrace_118283
  have hstable : (prefixWord ++ tailWord_118283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118283).length < 2 ^ (prefixWord ++ tailWord_118283).sum := by decide
  have hdescent : baseEnd_118283 < baseStart_118283 := by decide
  rcases family_descends (prefixWord ++ tailWord_118283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118341 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 5, 3]
def baseStart_118341 : Nat := 118140960795 + 118341 * 2 ^ 59
def prefixEnd_118341 : Nat := 4983230072969 + 3 ^ 40 * 118341 * 2
def baseEnd_118341 : Nat := 40510542755884482662177

theorem tailTrace_118341 : CollatzResearch.WordTrace tailWord_118341 prefixEnd_118341 40510542755884482662177 := by
  unfold tailWord_118341
  simp only [CollatzResearch.WordTrace]
  refine ⟨4316250864278242878826877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2877500576185495252551251 4316250864278242878826877)
  ·
    refine ⟨1618594074104341079560079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4316250864278242878826877 1618594074104341079560079)
    ·
      refine ⟨2427891111156511619340119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1618594074104341079560079 2427891111156511619340119)
      ·
        refine ⟨3641836666734767429010179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2427891111156511619340119 3641836666734767429010179)
        ·
          refine ⟨5462755000102151143515269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3641836666734767429010179 5462755000102151143515269)
          ·
            refine ⟨1024266562519153339409113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5462755000102151143515269 1024266562519153339409113)
            ·
              refine ⟨768199921889365004556835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1024266562519153339409113 768199921889365004556835)
              ·
                refine ⟨1152299882834047506835253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 768199921889365004556835 1152299882834047506835253)
                ·
                  refine ⟨108028114015691953765805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1152299882834047506835253 108028114015691953765805)
                  ·
                    refine ⟨40510542755884482662177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108028114015691953765805 40510542755884482662177)
                    ·
                      rfl

theorem cell22_118341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_118341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118341 prefixEnd_118341 := by exact prefixLift 118341
  have htrace : WordTrace (prefixWord ++ tailWord_118341) baseStart_118341 baseEnd_118341 := by
    simpa [prefixWord, tailWord_118341, baseEnd_118341] using wordTrace_append hprefix tailTrace_118341
  have hstable : (prefixWord ++ tailWord_118341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118341).length < 2 ^ (prefixWord ++ tailWord_118341).sum := by decide
  have hdescent : baseEnd_118341 < baseStart_118341 := by decide
  rcases family_descends (prefixWord ++ tailWord_118341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118371 : List Nat := [1, 1, 1, 5, 1, 3, 1, 4, 5]
def baseStart_118371 : Nat := 118140960795 + 118371 * 2 ^ 59
def prefixEnd_118371 : Nat := 4983230072969 + 3 ^ 40 * 118371 * 2
def baseEnd_118371 : Nat := 13506937456324801470695

theorem tailTrace_118371 : CollatzResearch.WordTrace tailWord_118371 prefixEnd_118371 13506937456324801470695 := by
  unfold tailWord_118371
  simp only [CollatzResearch.WordTrace]
  refine ⟨4317345054169558002418967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2878230036113038668279311 4317345054169558002418967)
  ·
    refine ⟨6476017581254337003628451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4317345054169558002418967 6476017581254337003628451)
    ·
      refine ⟨9714026371881505505442677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6476017581254337003628451 9714026371881505505442677)
      ·
        refine ⟨910689972363891141135251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9714026371881505505442677 910689972363891141135251)
        ·
          refine ⟨1366034958545836711702877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910689972363891141135251 1366034958545836711702877)
          ·
            refine ⟨512263109454688766888579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1366034958545836711702877 512263109454688766888579)
            ·
              refine ⟨768394664182033150332869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512263109454688766888579 768394664182033150332869)
              ·
                refine ⟨144073999534131215687413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 768394664182033150332869 144073999534131215687413)
                ·
                  refine ⟨13506937456324801470695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144073999534131215687413 13506937456324801470695)
                  ·
                    rfl

theorem cell22_118371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 5].length) (baseStart_118371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118371 prefixEnd_118371 := by exact prefixLift 118371
  have htrace : WordTrace (prefixWord ++ tailWord_118371) baseStart_118371 baseEnd_118371 := by
    simpa [prefixWord, tailWord_118371, baseEnd_118371] using wordTrace_append hprefix tailTrace_118371
  have hstable : (prefixWord ++ tailWord_118371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118371).length < 2 ^ (prefixWord ++ tailWord_118371).sum := by decide
  have hdescent : baseEnd_118371 < baseStart_118371 := by decide
  rcases family_descends (prefixWord ++ tailWord_118371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118386 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_118386 : Nat := 118140960795 + 118386 * 2 ^ 59
def prefixEnd_118386 : Nat := 4983230072969 + 3 ^ 40 * 118386 * 2
def baseEnd_118386 : Nat := 40525947175519365287039

theorem tailTrace_118386 : CollatzResearch.WordTrace tailWord_118386 prefixEnd_118386 40525947175519365287039 := by
  unfold tailWord_118386
  simp only [CollatzResearch.WordTrace]
  refine ⟨1079473037278803891053753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2878594766076810376143341 1079473037278803891053753)
  ·
    refine ⟨809604777959102918290315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1079473037278803891053753 809604777959102918290315)
    ·
      refine ⟨1214407166938654377435473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 809604777959102918290315 1214407166938654377435473)
      ·
        refine ⟨910805375203990783076605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1214407166938654377435473 910805375203990783076605)
        ·
          refine ⟨341552015701496543653727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 910805375203990783076605 341552015701496543653727)
          ·
            refine ⟨512328023552244815480591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341552015701496543653727 512328023552244815480591)
            ·
              refine ⟨768492035328367223220887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512328023552244815480591 768492035328367223220887)
              ·
                refine ⟨1152738052992550834831331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 768492035328367223220887 1152738052992550834831331)
                ·
                  refine ⟨1729107079488826252246997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1152738052992550834831331 1729107079488826252246997)
                  ·
                    refine ⟨40525947175519365287039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1729107079488826252246997 40525947175519365287039)
                    ·
                      rfl

theorem cell22_118386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_118386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118386 prefixEnd_118386 := by exact prefixLift 118386
  have htrace : WordTrace (prefixWord ++ tailWord_118386) baseStart_118386 baseEnd_118386 := by
    simpa [prefixWord, tailWord_118386, baseEnd_118386] using wordTrace_append hprefix tailTrace_118386
  have hstable : (prefixWord ++ tailWord_118386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118386).length < 2 ^ (prefixWord ++ tailWord_118386).sum := by decide
  have hdescent : baseEnd_118386 < baseStart_118386 := by decide
  rcases family_descends (prefixWord ++ tailWord_118386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118433 : List Nat := [1, 2, 3, 3, 2, 2, 2, 1, 6]
def baseStart_118433 : Nat := 118140960795 + 118433 * 2 ^ 59
def prefixEnd_118433 : Nat := 4983230072969 + 3 ^ 40 * 118433 * 2
def baseEnd_118433 : Nat := 13514012078675636453965

theorem tailTrace_118433 : CollatzResearch.WordTrace tailWord_118433 prefixEnd_118433 13514012078675636453965 := by
  unfold tailWord_118433
  simp only [CollatzResearch.WordTrace]
  refine ⟨4319606379944942591175953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2879737586629961727450635 4319606379944942591175953)
  ·
    refine ⟨3239704784958706943381965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4319606379944942591175953 3239704784958706943381965)
    ·
      refine ⟨1214889294359515103768237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3239704784958706943381965 1214889294359515103768237)
      ·
        refine ⟨455583485384818163913089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1214889294359515103768237 455583485384818163913089)
        ·
          refine ⟨341687614038613622934817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455583485384818163913089 341687614038613622934817)
          ·
            refine ⟨256265710528960217201113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341687614038613622934817 256265710528960217201113)
            ·
              refine ⟨192199282896720162900835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256265710528960217201113 192199282896720162900835)
              ·
                refine ⟨288298924345080244351253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192199282896720162900835 288298924345080244351253)
                ·
                  refine ⟨13514012078675636453965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 288298924345080244351253 13514012078675636453965)
                  ·
                    rfl

theorem cell22_118433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 6].length) (baseStart_118433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118433 prefixEnd_118433 := by exact prefixLift 118433
  have htrace : WordTrace (prefixWord ++ tailWord_118433) baseStart_118433 baseEnd_118433 := by
    simpa [prefixWord, tailWord_118433, baseEnd_118433] using wordTrace_append hprefix tailTrace_118433
  have hstable : (prefixWord ++ tailWord_118433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118433).length < 2 ^ (prefixWord ++ tailWord_118433).sum := by decide
  have hdescent : baseEnd_118433 < baseStart_118433 := by decide
  rcases family_descends (prefixWord ++ tailWord_118433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118448 : List Nat := [2, 1, 1, 1, 2, 1, 4, 5, 2, 3]
def baseStart_118448 : Nat := 118140960795 + 118448 * 2 ^ 59
def prefixEnd_118448 : Nat := 4983230072969 + 3 ^ 40 * 118448 * 2
def baseEnd_118448 : Nat := 40547171042571870236849

theorem tailTrace_118448 : CollatzResearch.WordTrace tailWord_118448 prefixEnd_118448 40547171042571870236849 := by
  unfold tailWord_118448
  simp only [CollatzResearch.WordTrace]
  refine ⟨2160076737445300076485999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2880102316593733435314665 2160076737445300076485999)
  ·
    refine ⟨3240115106167950114728999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2160076737445300076485999 3240115106167950114728999)
    ·
      refine ⟨4860172659251925172093499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3240115106167950114728999 4860172659251925172093499)
      ·
        refine ⟨7290258988877887758140249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4860172659251925172093499 7290258988877887758140249)
        ·
          refine ⟨5467694241658415818605187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7290258988877887758140249 5467694241658415818605187)
          ·
            refine ⟨8201541362487623727907781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5467694241658415818605187 8201541362487623727907781)
            ·
              refine ⟨1537789005466429448982709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8201541362487623727907781 1537789005466429448982709)
              ·
                refine ⟨144167719262477760842129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1537789005466429448982709 144167719262477760842129)
                ·
                  refine ⟨108125789446858320631597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144167719262477760842129 108125789446858320631597)
                  ·
                    refine ⟨40547171042571870236849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108125789446858320631597 40547171042571870236849)
                    ·
                      rfl

theorem cell22_118448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 2, 3].length) (baseStart_118448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118448 prefixEnd_118448 := by exact prefixLift 118448
  have htrace : WordTrace (prefixWord ++ tailWord_118448) baseStart_118448 baseEnd_118448 := by
    simpa [prefixWord, tailWord_118448, baseEnd_118448] using wordTrace_append hprefix tailTrace_118448
  have hstable : (prefixWord ++ tailWord_118448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118448).length < 2 ^ (prefixWord ++ tailWord_118448).sum := by decide
  have hdescent : baseEnd_118448 < baseStart_118448 := by decide
  rcases family_descends (prefixWord ++ tailWord_118448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118461 : List Nat := [1, 4, 1, 2, 1, 2, 3, 8]
def baseStart_118461 : Nat := 118140960795 + 118461 * 2 ^ 59
def prefixEnd_118461 : Nat := 4983230072969 + 3 ^ 40 * 118461 * 2
def baseEnd_118461 : Nat := 4505735689804907740201

theorem tailTrace_118461 : CollatzResearch.WordTrace tailWord_118461 prefixEnd_118461 4505735689804907740201 := by
  unfold tailWord_118461
  simp only [CollatzResearch.WordTrace]
  refine ⟨4320627623843503373195237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2880418415895668915463491 4320627623843503373195237)
  ·
    refine ⟨810117679470656882474107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4320627623843503373195237 810117679470656882474107)
    ·
      refine ⟨1215176519205985323711161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 810117679470656882474107 1215176519205985323711161)
      ·
        refine ⟨911382389404488992783371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1215176519205985323711161 911382389404488992783371)
        ·
          refine ⟨1367073584106733489175057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911382389404488992783371 1367073584106733489175057)
          ·
            refine ⟨1025305188080050116881293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1367073584106733489175057 1025305188080050116881293)
            ·
              refine ⟨384489445530018793830485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1025305188080050116881293 384489445530018793830485)
              ·
                refine ⟨4505735689804907740201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 384489445530018793830485 4505735689804907740201)
                ·
                  rfl

theorem cell22_118461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 8].length) (baseStart_118461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118461 prefixEnd_118461 := by exact prefixLift 118461
  have htrace : WordTrace (prefixWord ++ tailWord_118461) baseStart_118461 baseEnd_118461 := by
    simpa [prefixWord, tailWord_118461, baseEnd_118461] using wordTrace_append hprefix tailTrace_118461
  have hstable : (prefixWord ++ tailWord_118461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118461).length < 2 ^ (prefixWord ++ tailWord_118461).sum := by decide
  have hdescent : baseEnd_118461 < baseStart_118461 := by decide
  rcases family_descends (prefixWord ++ tailWord_118461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118499 : List Nat := [1, 1, 1, 7, 2, 2, 2, 1, 2, 3]
def baseStart_118499 : Nat := 118140960795 + 118499 * 2 ^ 59
def prefixEnd_118499 : Nat := 4983230072969 + 3 ^ 40 * 118499 * 2
def baseEnd_118499 : Nat := 40564629384824737211693

theorem tailTrace_118499 : CollatzResearch.WordTrace tailWord_118499 prefixEnd_118499 40564629384824737211693 := by
  unfold tailWord_118499
  simp only [CollatzResearch.WordTrace]
  refine ⟨4322013597705835863078551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2881342398470557242052367 4322013597705835863078551)
  ·
    refine ⟨6483020396558753794617827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4322013597705835863078551 6483020396558753794617827)
    ·
      refine ⟨9724530594838130691926741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6483020396558753794617827 9724530594838130691926741)
      ·
        refine ⟨227918685816518688092033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 9724530594838130691926741 227918685816518688092033)
        ·
          refine ⟨170939014362389016069025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227918685816518688092033 170939014362389016069025)
          ·
            refine ⟨128204260771791762051769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170939014362389016069025 128204260771791762051769)
            ·
              refine ⟨96153195578843821538827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128204260771791762051769 96153195578843821538827)
              ·
                refine ⟨144229793368265732308241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96153195578843821538827 144229793368265732308241)
                ·
                  refine ⟨108172345026199299231181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144229793368265732308241 108172345026199299231181)
                  ·
                    refine ⟨40564629384824737211693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108172345026199299231181 40564629384824737211693)
                    ·
                      rfl

theorem cell22_118499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 2, 3].length) (baseStart_118499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118499 prefixEnd_118499 := by exact prefixLift 118499
  have htrace : WordTrace (prefixWord ++ tailWord_118499) baseStart_118499 baseEnd_118499 := by
    simpa [prefixWord, tailWord_118499, baseEnd_118499] using wordTrace_append hprefix tailTrace_118499
  have hstable : (prefixWord ++ tailWord_118499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118499).length < 2 ^ (prefixWord ++ tailWord_118499).sum := by decide
  have hdescent : baseEnd_118499 < baseStart_118499 := by decide
  rcases family_descends (prefixWord ++ tailWord_118499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118521 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 6, 5]
def baseStart_118521 : Nat := 118140960795 + 118521 * 2 ^ 59
def prefixEnd_118521 : Nat := 4983230072969 + 3 ^ 40 * 118521 * 2
def baseEnd_118521 : Nat := 40572160434424013161625

theorem tailTrace_118521 : CollatzResearch.WordTrace tailWord_118521 prefixEnd_118521 40572160434424013161625 := by
  unfold tailWord_118521
  simp only [CollatzResearch.WordTrace]
  refine ⟨4322816003626133620379417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2881877335750755746919611 4322816003626133620379417)
  ·
    refine ⟨3242112002719600215284563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4322816003626133620379417 3242112002719600215284563)
    ·
      refine ⟨4863168004079400322926845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3242112002719600215284563 4863168004079400322926845)
      ·
        refine ⟨1823688001529775121097567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4863168004079400322926845 1823688001529775121097567)
        ·
          refine ⟨2735532002294662681646351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1823688001529775121097567 2735532002294662681646351)
          ·
            refine ⟨4103298003441994022469527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2735532002294662681646351 4103298003441994022469527)
            ·
              refine ⟨6154947005162991033704291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4103298003441994022469527 6154947005162991033704291)
              ·
                refine ⟨9232420507744486550556437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6154947005162991033704291 9232420507744486550556437)
                ·
                  refine ⟨432769711300522807057333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9232420507744486550556437 432769711300522807057333)
                  ·
                    refine ⟨40572160434424013161625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 432769711300522807057333 40572160434424013161625)
                    ·
                      rfl

theorem cell22_118521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_118521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118521 prefixEnd_118521 := by exact prefixLift 118521
  have htrace : WordTrace (prefixWord ++ tailWord_118521) baseStart_118521 baseEnd_118521 := by
    simpa [prefixWord, tailWord_118521, baseEnd_118521] using wordTrace_append hprefix tailTrace_118521
  have hstable : (prefixWord ++ tailWord_118521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118521).length < 2 ^ (prefixWord ++ tailWord_118521).sum := by decide
  have hdescent : baseEnd_118521 < baseStart_118521 := by decide
  rcases family_descends (prefixWord ++ tailWord_118521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118568 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 8]
def baseStart_118568 : Nat := 118140960795 + 118568 * 2 ^ 59
def prefixEnd_118568 : Nat := 4983230072969 + 3 ^ 40 * 118568 * 2
def baseEnd_118568 : Nat := 13529416498310519078827

theorem tailTrace_118568 : CollatzResearch.WordTrace tailWord_118568 prefixEnd_118568 13529416498310519078827 := by
  unfold tailWord_118568
  simp only [CollatzResearch.WordTrace]
  refine ⟨2162265117227930323670179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2883020156303907098226905 2162265117227930323670179)
  ·
    refine ⟨3243397675841895485505269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2162265117227930323670179 3243397675841895485505269)
    ·
      refine ⟨304068532110177701766119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3243397675841895485505269 304068532110177701766119)
      ·
        refine ⟨456102798165266552649179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304068532110177701766119 456102798165266552649179)
        ·
          refine ⟨684154197247899828973769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456102798165266552649179 684154197247899828973769)
          ·
            refine ⟨513115647935924871730327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 684154197247899828973769 513115647935924871730327)
            ·
              refine ⟨769673471903887307595491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513115647935924871730327 769673471903887307595491)
              ·
                refine ⟨1154510207855830961393237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769673471903887307595491 1154510207855830961393237)
                ·
                  refine ⟨13529416498310519078827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1154510207855830961393237 13529416498310519078827)
                  ·
                    rfl

theorem cell22_118568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 8].length) (baseStart_118568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118568 prefixEnd_118568 := by exact prefixLift 118568
  have htrace : WordTrace (prefixWord ++ tailWord_118568) baseStart_118568 baseEnd_118568 := by
    simpa [prefixWord, tailWord_118568, baseEnd_118568] using wordTrace_append hprefix tailTrace_118568
  have hstable : (prefixWord ++ tailWord_118568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118568).length < 2 ^ (prefixWord ++ tailWord_118568).sum := by decide
  have hdescent : baseEnd_118568 < baseStart_118568 := by decide
  rcases family_descends (prefixWord ++ tailWord_118568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118600 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 4, 3]
def baseStart_118600 : Nat := 118140960795 + 118600 * 2 ^ 59
def prefixEnd_118600 : Nat := 4983230072969 + 3 ^ 40 * 118600 * 2
def baseEnd_118600 : Nat := 40599203748894140436383

theorem tailTrace_118600 : CollatzResearch.WordTrace tailWord_118600 prefixEnd_118600 40599203748894140436383 := by
  unfold tailWord_118600
  simp only [CollatzResearch.WordTrace]
  refine ⟨2162848685169965056252627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2883798246893286741670169 2162848685169965056252627)
  ·
    refine ⟨3244273027754947584378941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2162848685169965056252627 3244273027754947584378941)
    ·
      refine ⟨1216602385408105344142103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3244273027754947584378941 1216602385408105344142103)
      ·
        refine ⟨1824903578112158016213155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1216602385408105344142103 1824903578112158016213155)
        ·
          refine ⟨2737355367168237024319733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1824903578112158016213155 2737355367168237024319733)
          ·
            refine ⟨256627065672022221029975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2737355367168237024319733 256627065672022221029975)
            ·
              refine ⟨384940598508033331544963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256627065672022221029975 384940598508033331544963)
              ·
                refine ⟨577410897762049997317445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384940598508033331544963 577410897762049997317445)
                ·
                  refine ⟨108264543330384374497021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 577410897762049997317445 108264543330384374497021)
                  ·
                    refine ⟨40599203748894140436383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108264543330384374497021 40599203748894140436383)
                    ·
                      rfl

theorem cell22_118600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_118600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118600 prefixEnd_118600 := by exact prefixLift 118600
  have htrace : WordTrace (prefixWord ++ tailWord_118600) baseStart_118600 baseEnd_118600 := by
    simpa [prefixWord, tailWord_118600, baseEnd_118600] using wordTrace_append hprefix tailTrace_118600
  have hstable : (prefixWord ++ tailWord_118600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118600).length < 2 ^ (prefixWord ++ tailWord_118600).sum := by decide
  have hdescent : baseEnd_118600 < baseStart_118600 := by decide
  rcases family_descends (prefixWord ++ tailWord_118600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118617 : List Nat := [1, 2, 1, 2, 2, 3, 5, 1, 2, 3]
def baseStart_118617 : Nat := 118140960795 + 118617 * 2 ^ 59
def prefixEnd_118617 : Nat := 4983230072969 + 3 ^ 40 * 118617 * 2
def baseEnd_118617 : Nat := 40605023196311762761331

theorem tailTrace_118617 : CollatzResearch.WordTrace tailWord_118617 prefixEnd_118617 40605023196311762761331 := by
  unfold tailWord_118617
  simp only [CollatzResearch.WordTrace]
  refine ⟨4326317411278342015874105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2884211607518894677249403 4326317411278342015874105)
  ·
    refine ⟨3244738058458756511905579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4326317411278342015874105 3244738058458756511905579)
    ·
      refine ⟨4867107087688134767858369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3244738058458756511905579 4867107087688134767858369)
      ·
        refine ⟨3650330315766101075893777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4867107087688134767858369 3650330315766101075893777)
        ·
          refine ⟨2737747736824575806920333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3650330315766101075893777 2737747736824575806920333)
          ·
            refine ⟨1026655401309215927595125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2737747736824575806920333 1026655401309215927595125)
            ·
              refine ⟨96248943872738993212043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1026655401309215927595125 96248943872738993212043)
              ·
                refine ⟨144373415809108489818065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96248943872738993212043 144373415809108489818065)
                ·
                  refine ⟨108280061856831367363549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144373415809108489818065 108280061856831367363549)
                  ·
                    refine ⟨40605023196311762761331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108280061856831367363549 40605023196311762761331)
                    ·
                      rfl

theorem cell22_118617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 2, 3].length) (baseStart_118617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118617 prefixEnd_118617 := by exact prefixLift 118617
  have htrace : WordTrace (prefixWord ++ tailWord_118617) baseStart_118617 baseEnd_118617 := by
    simpa [prefixWord, tailWord_118617, baseEnd_118617] using wordTrace_append hprefix tailTrace_118617
  have hstable : (prefixWord ++ tailWord_118617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118617).length < 2 ^ (prefixWord ++ tailWord_118617).sum := by decide
  have hdescent : baseEnd_118617 < baseStart_118617 := by decide
  rcases family_descends (prefixWord ++ tailWord_118617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118673 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 2, 5]
def baseStart_118673 : Nat := 118140960795 + 118673 * 2 ^ 59
def prefixEnd_118673 : Nat := 4983230072969 + 3 ^ 40 * 118673 * 2
def baseEnd_118673 : Nat := 40624193140746283361159

theorem tailTrace_118673 : CollatzResearch.WordTrace tailWord_118673 prefixEnd_118673 40624193140746283361159 := by
  unfold tailWord_118673
  simp only [CollatzResearch.WordTrace]
  refine ⟨4328359899075463579912673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2885573266050309053275115 4328359899075463579912673)
  ·
    refine ⟨3246269924306597684934505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4328359899075463579912673 3246269924306597684934505)
    ·
      refine ⟨2434702443229948263700879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3246269924306597684934505 2434702443229948263700879)
      ·
        refine ⟨3652053664844922395551319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2434702443229948263700879 3652053664844922395551319)
        ·
          refine ⟨5478080497267383593326979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3652053664844922395551319 5478080497267383593326979)
          ·
            refine ⟨8217120745901075389990469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5478080497267383593326979 8217120745901075389990469)
            ·
              refine ⟨1540710139856451635623213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8217120745901075389990469 1540710139856451635623213)
              ·
                refine ⟨577766302446169363358705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1540710139856451635623213 577766302446169363358705)
                ·
                  refine ⟨433324726834627022519029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577766302446169363358705 433324726834627022519029)
                  ·
                    refine ⟨40624193140746283361159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 433324726834627022519029 40624193140746283361159)
                    ·
                      rfl

theorem cell22_118673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_118673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118673 prefixEnd_118673 := by exact prefixLift 118673
  have htrace : WordTrace (prefixWord ++ tailWord_118673) baseStart_118673 baseEnd_118673 := by
    simpa [prefixWord, tailWord_118673, baseEnd_118673] using wordTrace_append hprefix tailTrace_118673
  have hstable : (prefixWord ++ tailWord_118673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118673).length < 2 ^ (prefixWord ++ tailWord_118673).sum := by decide
  have hdescent : baseEnd_118673 < baseStart_118673 := by decide
  rcases family_descends (prefixWord ++ tailWord_118673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118735 : List Nat := [1, 1, 2, 1, 1, 5, 4, 1, 1, 5]
def baseStart_118735 : Nat := 118140960795 + 118735 * 2 ^ 59
def prefixEnd_118735 : Nat := 4983230072969 + 3 ^ 40 * 118735 * 2
def baseEnd_118735 : Nat := 40645417007798788310969

theorem tailTrace_118735 : CollatzResearch.WordTrace tailWord_118735 prefixEnd_118735 40645417007798788310969 := by
  unfold tailWord_118735
  simp only [CollatzResearch.WordTrace]
  refine ⟨4330621224850848168669659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2887080816567232112446439 4330621224850848168669659)
  ·
    refine ⟨6495931837276272253004489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4330621224850848168669659 6495931837276272253004489)
    ·
      refine ⟨4871948877957204189753367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6495931837276272253004489 4871948877957204189753367)
      ·
        refine ⟨7307923316935806284630051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4871948877957204189753367 7307923316935806284630051)
        ·
          refine ⟨10961884975403709426945077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7307923316935806284630051 10961884975403709426945077)
          ·
            refine ⟨1027676716444097758776101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10961884975403709426945077 1027676716444097758776101)
            ·
              refine ⟨192689384333268329770519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1027676716444097758776101 192689384333268329770519)
              ·
                refine ⟨289034076499902494655779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192689384333268329770519 289034076499902494655779)
                ·
                  refine ⟨433551114749853741983669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 289034076499902494655779 433551114749853741983669)
                  ·
                    refine ⟨40645417007798788310969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 433551114749853741983669 40645417007798788310969)
                    ·
                      rfl

theorem cell22_118735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 5].length) (baseStart_118735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118735 prefixEnd_118735 := by exact prefixLift 118735
  have htrace : WordTrace (prefixWord ++ tailWord_118735) baseStart_118735 baseEnd_118735 := by
    simpa [prefixWord, tailWord_118735, baseEnd_118735] using wordTrace_append hprefix tailTrace_118735
  have hstable : (prefixWord ++ tailWord_118735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118735).length < 2 ^ (prefixWord ++ tailWord_118735).sum := by decide
  have hdescent : baseEnd_118735 < baseStart_118735 := by decide
  rcases family_descends (prefixWord ++ tailWord_118735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118763 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 1, 9]
def baseStart_118763 : Nat := 118140960795 + 118763 * 2 ^ 59
def prefixEnd_118763 : Nat := 4983230072969 + 3 ^ 40 * 118763 * 2
def baseEnd_118763 : Nat := 40655001980016048610883

theorem tailTrace_118763 : CollatzResearch.WordTrace tailWord_118763 prefixEnd_118763 40655001980016048610883 := by
  unfold tailWord_118763
  simp only [CollatzResearch.WordTrace]
  refine ⟨4331642468749408950688943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2887761645832939300459295 4331642468749408950688943)
  ·
    refine ⟨6497463703124113426033415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4331642468749408950688943 6497463703124113426033415)
    ·
      refine ⟨9746195554686170139050123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6497463703124113426033415 9746195554686170139050123)
      ·
        refine ⟨14619293332029255208575185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9746195554686170139050123 14619293332029255208575185)
        ·
          refine ⟨10964469999021941406431389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14619293332029255208575185 10964469999021941406431389)
          ·
            refine ⟨4111676249633228027411771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10964469999021941406431389 4111676249633228027411771)
            ·
              refine ⟨6167514374449842041117657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4111676249633228027411771 6167514374449842041117657)
              ·
                refine ⟨4625635780837381530838243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6167514374449842041117657 4625635780837381530838243)
                ·
                  refine ⟨6938453671256072296257365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4625635780837381530838243 6938453671256072296257365)
                  ·
                    refine ⟨40655001980016048610883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 6938453671256072296257365 40655001980016048610883)
                    ·
                      rfl

theorem cell22_118763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 9].length) (baseStart_118763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118763 prefixEnd_118763 := by exact prefixLift 118763
  have htrace : WordTrace (prefixWord ++ tailWord_118763) baseStart_118763 baseEnd_118763 := by
    simpa [prefixWord, tailWord_118763, baseEnd_118763] using wordTrace_append hprefix tailTrace_118763
  have hstable : (prefixWord ++ tailWord_118763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118763).length < 2 ^ (prefixWord ++ tailWord_118763).sum := by decide
  have hdescent : baseEnd_118763 < baseStart_118763 := by decide
  rcases family_descends (prefixWord ++ tailWord_118763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118790 : List Nat := [6, 2, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_118790 : Nat := 118140960795 + 118790 * 2 ^ 59
def prefixEnd_118790 : Nat := 4983230072969 + 3 ^ 40 * 118790 * 2
def baseEnd_118790 : Nat := 40664244631796978185801

theorem tailTrace_118790 : CollatzResearch.WordTrace tailWord_118790 prefixEnd_118790 40664244631796978185801 := by
  unfold tailWord_118790
  simp only [CollatzResearch.WordTrace]
  refine ⟨135394601239112267560057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2888418159767728374614549 135394601239112267560057)
  ·
    refine ⟨101545950929334200670043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135394601239112267560057 101545950929334200670043)
    ·
      refine ⟨152318926394001301005065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101545950929334200670043 152318926394001301005065)
      ·
        refine ⟨114239194795500975753799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152318926394001301005065 114239194795500975753799)
        ·
          refine ⟨171358792193251463630699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114239194795500975753799 171358792193251463630699)
          ·
            refine ⟨257038188289877195446049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171358792193251463630699 257038188289877195446049)
            ·
              refine ⟨192778641217407896584537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257038188289877195446049 192778641217407896584537)
              ·
                refine ⟨144583980913055922438403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192778641217407896584537 144583980913055922438403)
                ·
                  refine ⟨216875971369583883657605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144583980913055922438403 216875971369583883657605)
                  ·
                    refine ⟨40664244631796978185801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 216875971369583883657605 40664244631796978185801)
                    ·
                      rfl

theorem cell22_118790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_118790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118790 prefixEnd_118790 := by exact prefixLift 118790
  have htrace : WordTrace (prefixWord ++ tailWord_118790) baseStart_118790 baseEnd_118790 := by
    simpa [prefixWord, tailWord_118790, baseEnd_118790] using wordTrace_append hprefix tailTrace_118790
  have hstable : (prefixWord ++ tailWord_118790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118790).length < 2 ^ (prefixWord ++ tailWord_118790).sum := by decide
  have hdescent : baseEnd_118790 < baseStart_118790 := by decide
  rcases family_descends (prefixWord ++ tailWord_118790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118810 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 7]
def baseStart_118810 : Nat := 118140960795 + 118810 * 2 ^ 59
def prefixEnd_118810 : Nat := 4983230072969 + 3 ^ 40 * 118810 * 2
def baseEnd_118810 : Nat := 13557030346841197561913

theorem tailTrace_118810 : CollatzResearch.WordTrace tailWord_118810 prefixEnd_118810 13557030346841197561913 := by
  unfold tailWord_118810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1083339174894783994412471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2888904466386090651766589 1083339174894783994412471)
  ·
    refine ⟨1625008762342175991618707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1083339174894783994412471 1625008762342175991618707)
    ·
      refine ⟨2437513143513263987428061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1625008762342175991618707 2437513143513263987428061)
      ·
        refine ⟨914067428817473995285523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2437513143513263987428061 914067428817473995285523)
        ·
          refine ⟨1371101143226210992928285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914067428817473995285523 1371101143226210992928285)
          ·
            refine ⟨514162928709829122348107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1371101143226210992928285 514162928709829122348107)
            ·
              refine ⟨771244393064743683522161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514162928709829122348107 771244393064743683522161)
              ·
                refine ⟨578433294798557762641621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 771244393064743683522161 578433294798557762641621)
                ·
                  refine ⟨13557030346841197561913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 578433294798557762641621 13557030346841197561913)
                  ·
                    rfl

theorem cell22_118810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_118810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118810 prefixEnd_118810 := by exact prefixLift 118810
  have htrace : WordTrace (prefixWord ++ tailWord_118810) baseStart_118810 baseEnd_118810 := by
    simpa [prefixWord, tailWord_118810, baseEnd_118810] using wordTrace_append hprefix tailTrace_118810
  have hstable : (prefixWord ++ tailWord_118810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118810).length < 2 ^ (prefixWord ++ tailWord_118810).sum := by decide
  have hdescent : baseEnd_118810 < baseStart_118810 := by decide
  rcases family_descends (prefixWord ++ tailWord_118810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118855 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 8]
def baseStart_118855 : Nat := 118140960795 + 118855 * 2 ^ 59
def prefixEnd_118855 : Nat := 4983230072969 + 3 ^ 40 * 118855 * 2
def baseEnd_118855 : Nat := 13562165153386158436867

theorem tailTrace_118855 : CollatzResearch.WordTrace tailWord_118855 prefixEnd_118855 13562165153386158436867 := by
  unfold tailWord_118855
  simp only [CollatzResearch.WordTrace]
  refine ⟨4334997984416108663038019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2889998656277405775358679 4334997984416108663038019)
  ·
    refine ⟨6502496976624162994557029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4334997984416108663038019 6502496976624162994557029)
    ·
      refine ⟨1219218183117030561479443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6502496976624162994557029 1219218183117030561479443)
      ·
        refine ⟨1828827274675545842219165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1219218183117030561479443 1828827274675545842219165)
        ·
          refine ⟨685810228003329690832187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1828827274675545842219165 685810228003329690832187)
          ·
            refine ⟨1028715342004994536248281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685810228003329690832187 1028715342004994536248281)
            ·
              refine ⟨771536506503745902186211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1028715342004994536248281 771536506503745902186211)
              ·
                refine ⟨1157304759755618853279317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771536506503745902186211 1157304759755618853279317)
                ·
                  refine ⟨13562165153386158436867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1157304759755618853279317 13562165153386158436867)
                  ·
                    rfl

theorem cell22_118855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 8].length) (baseStart_118855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118855 prefixEnd_118855 := by exact prefixLift 118855
  have htrace : WordTrace (prefixWord ++ tailWord_118855) baseStart_118855 baseEnd_118855 := by
    simpa [prefixWord, tailWord_118855, baseEnd_118855] using wordTrace_append hprefix tailTrace_118855
  have hstable : (prefixWord ++ tailWord_118855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118855).length < 2 ^ (prefixWord ++ tailWord_118855).sum := by decide
  have hdescent : baseEnd_118855 < baseStart_118855 := by decide
  rcases family_descends (prefixWord ++ tailWord_118855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118874 : List Nat := [3, 1, 1, 2, 1, 1, 7, 1, 1, 4]
def baseStart_118874 : Nat := 118140960795 + 118874 * 2 ^ 59
def prefixEnd_118874 : Nat := 4983230072969 + 3 ^ 40 * 118874 * 2
def baseEnd_118874 : Nat := 40692999548448759085543

theorem tailTrace_118874 : CollatzResearch.WordTrace tailWord_118874 prefixEnd_118874 40692999548448759085543 := by
  unfold tailWord_118874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1083922742836818726994919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2890460647564849938653117 1083922742836818726994919)
  ·
    refine ⟨1625884114255228090492379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1083922742836818726994919 1625884114255228090492379)
    ·
      refine ⟨2438826171382842135738569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1625884114255228090492379 2438826171382842135738569)
      ·
        refine ⟨1829119628537131601803927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2438826171382842135738569 1829119628537131601803927)
        ·
          refine ⟨2743679442805697402705891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829119628537131601803927 2743679442805697402705891)
          ·
            refine ⟨4115519164208546104058837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743679442805697402705891 4115519164208546104058837)
            ·
              refine ⟨96457480411137799313879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4115519164208546104058837 96457480411137799313879)
              ·
                refine ⟨144686220616706698970819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96457480411137799313879 144686220616706698970819)
                ·
                  refine ⟨217029330925060048456229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144686220616706698970819 217029330925060048456229)
                  ·
                    refine ⟨40692999548448759085543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 217029330925060048456229 40692999548448759085543)
                    ·
                      rfl

theorem cell22_118874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 1, 4].length) (baseStart_118874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118874 prefixEnd_118874 := by exact prefixLift 118874
  have htrace : WordTrace (prefixWord ++ tailWord_118874) baseStart_118874 baseEnd_118874 := by
    simpa [prefixWord, tailWord_118874, baseEnd_118874] using wordTrace_append hprefix tailTrace_118874
  have hstable : (prefixWord ++ tailWord_118874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118874).length < 2 ^ (prefixWord ++ tailWord_118874).sum := by decide
  have hdescent : baseEnd_118874 < baseStart_118874 := by decide
  rcases family_descends (prefixWord ++ tailWord_118874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118878 : List Nat := [4, 4, 1, 1, 2, 1, 2, 2, 5]
def baseStart_118878 : Nat := 118140960795 + 118878 * 2 ^ 59
def prefixEnd_118878 : Nat := 4983230072969 + 3 ^ 40 * 118878 * 2
def baseEnd_118878 : Nat := 13564789610064693995177

theorem tailTrace_118878 : CollatzResearch.WordTrace tailWord_118878 prefixEnd_118878 13564789610064693995177 := by
  unfold tailWord_118878
  simp only [CollatzResearch.WordTrace]
  refine ⟨541979607916597948890661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2890557908888522394083525 541979607916597948890661)
  ·
    refine ⟨101621176484362115416999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 541979607916597948890661 101621176484362115416999)
    ·
      refine ⟨152431764726543173125499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101621176484362115416999 152431764726543173125499)
      ·
        refine ⟨228647647089814759688249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152431764726543173125499 228647647089814759688249)
        ·
          refine ⟨171485735317361069766187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228647647089814759688249 171485735317361069766187)
          ·
            refine ⟨257228602976041604649281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171485735317361069766187 257228602976041604649281)
            ·
              refine ⟨192921452232031203486961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257228602976041604649281 192921452232031203486961)
              ·
                refine ⟨144691089174023402615221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192921452232031203486961 144691089174023402615221)
                ·
                  refine ⟨13564789610064693995177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144691089174023402615221 13564789610064693995177)
                  ·
                    rfl

theorem cell22_118878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_118878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118878 prefixEnd_118878 := by exact prefixLift 118878
  have htrace : WordTrace (prefixWord ++ tailWord_118878) baseStart_118878 baseEnd_118878 := by
    simpa [prefixWord, tailWord_118878, baseEnd_118878] using wordTrace_append hprefix tailTrace_118878
  have hstable : (prefixWord ++ tailWord_118878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118878).length < 2 ^ (prefixWord ++ tailWord_118878).sum := by decide
  have hdescent : baseEnd_118878 < baseStart_118878 := by decide
  rcases family_descends (prefixWord ++ tailWord_118878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118882 : List Nat := [3, 3, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_118882 : Nat := 118140960795 + 118882 * 2 ^ 59
def prefixEnd_118882 : Nat := 4983230072969 + 3 ^ 40 * 118882 * 2
def baseEnd_118882 : Nat := 40695738111939404885519

theorem tailTrace_118882 : CollatzResearch.WordTrace tailWord_118882 prefixEnd_118882 40695738111939404885519 := by
  unfold tailWord_118882
  simp only [CollatzResearch.WordTrace]
  refine ⟨1083995688829573068567725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2890655170212194849513933 1083995688829573068567725)
  ·
    refine ⟨406498383311089900712897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1083995688829573068567725 406498383311089900712897)
    ·
      refine ⟨304873787483317425534673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406498383311089900712897 304873787483317425534673)
      ·
        refine ⟨228655340612488069151005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304873787483317425534673 228655340612488069151005)
        ·
          refine ⟨85745752729683025931627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228655340612488069151005 85745752729683025931627)
          ·
            refine ⟨128618629094524538897441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85745752729683025931627 128618629094524538897441)
            ·
              refine ⟨96463971820893404173081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128618629094524538897441 96463971820893404173081)
              ·
                refine ⟨72347978865670053129811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96463971820893404173081 72347978865670053129811)
                ·
                  refine ⟨108521968298505079694717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72347978865670053129811 108521968298505079694717)
                  ·
                    refine ⟨40695738111939404885519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108521968298505079694717 40695738111939404885519)
                    ·
                      rfl

theorem cell22_118882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_118882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118882 prefixEnd_118882 := by exact prefixLift 118882
  have htrace : WordTrace (prefixWord ++ tailWord_118882) baseStart_118882 baseEnd_118882 := by
    simpa [prefixWord, tailWord_118882, baseEnd_118882] using wordTrace_append hprefix tailTrace_118882
  have hstable : (prefixWord ++ tailWord_118882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118882).length < 2 ^ (prefixWord ++ tailWord_118882).sum := by decide
  have hdescent : baseEnd_118882 < baseStart_118882 := by decide
  rcases family_descends (prefixWord ++ tailWord_118882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118938 : List Nat := [3, 1, 1, 5, 2, 2, 1, 2, 2, 3]
def baseStart_118938 : Nat := 118140960795 + 118938 * 2 ^ 59
def prefixEnd_118938 : Nat := 4983230072969 + 3 ^ 40 * 118938 * 2
def baseEnd_118938 : Nat := 40714908056373925485347

theorem tailTrace_118938 : CollatzResearch.WordTrace tailWord_118938 prefixEnd_118938 40714908056373925485347 := by
  unfold tailWord_118938
  simp only [CollatzResearch.WordTrace]
  refine ⟨1084506310778853459577367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2892016828743609225539645 1084506310778853459577367)
  ·
    refine ⟨1626759466168280189366051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1084506310778853459577367 1626759466168280189366051)
    ·
      refine ⟨2440139199252420284049077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1626759466168280189366051 2440139199252420284049077)
      ·
        refine ⟨228763049929914401629601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2440139199252420284049077 228763049929914401629601)
        ·
          refine ⟨171572287447435801222201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228763049929914401629601 171572287447435801222201)
          ·
            refine ⟨128679215585576850916651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171572287447435801222201 128679215585576850916651)
            ·
              refine ⟨193018823378365276374977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128679215585576850916651 193018823378365276374977)
              ·
                refine ⟨144764117533773957281233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193018823378365276374977 144764117533773957281233)
                ·
                  refine ⟨108573088150330467960925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144764117533773957281233 108573088150330467960925)
                  ·
                    refine ⟨40714908056373925485347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108573088150330467960925 40714908056373925485347)
                    ·
                      rfl

theorem cell22_118938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_118938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118938 prefixEnd_118938 := by exact prefixLift 118938
  have htrace : WordTrace (prefixWord ++ tailWord_118938) baseStart_118938 baseEnd_118938 := by
    simpa [prefixWord, tailWord_118938, baseEnd_118938] using wordTrace_append hprefix tailTrace_118938
  have hstable : (prefixWord ++ tailWord_118938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118938).length < 2 ^ (prefixWord ++ tailWord_118938).sum := by decide
  have hdescent : baseEnd_118938 < baseStart_118938 := by decide
  rcases family_descends (prefixWord ++ tailWord_118938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118949 : List Nat := [1, 3, 1, 2, 1, 3, 4, 1, 3, 3]
def baseStart_118949 : Nat := 118140960795 + 118949 * 2 ^ 59
def prefixEnd_118949 : Nat := 4983230072969 + 3 ^ 40 * 118949 * 2
def baseEnd_118949 : Nat := 40718673581173563460313

theorem tailTrace_118949 : CollatzResearch.WordTrace tailWord_118949 prefixEnd_118949 40718673581173563460313 := by
  unfold tailWord_118949
  simp only [CollatzResearch.WordTrace]
  refine ⟨4338426446075562716959901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2892284297383708477973267 4338426446075562716959901)
  ·
    refine ⟨1626909917278336018859963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4338426446075562716959901 1626909917278336018859963)
    ·
      refine ⟨2440364875917504028289945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1626909917278336018859963 2440364875917504028289945)
      ·
        refine ⟨1830273656938128021217459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2440364875917504028289945 1830273656938128021217459)
        ·
          refine ⟨2745410485407192031826189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1830273656938128021217459 2745410485407192031826189)
          ·
            refine ⟨1029528932027697011934821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2745410485407192031826189 1029528932027697011934821)
            ·
              refine ⟨193036674755193189737779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1029528932027697011934821 193036674755193189737779)
              ·
                refine ⟨289555012132789784606669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193036674755193189737779 289555012132789784606669)
                ·
                  refine ⟨108583129549796169227501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289555012132789784606669 108583129549796169227501)
                  ·
                    refine ⟨40718673581173563460313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108583129549796169227501 40718673581173563460313)
                    ·
                      rfl

theorem cell22_118949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_118949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_118949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_118949 prefixEnd_118949 := by exact prefixLift 118949
  have htrace : WordTrace (prefixWord ++ tailWord_118949) baseStart_118949 baseEnd_118949 := by
    simpa [prefixWord, tailWord_118949, baseEnd_118949] using wordTrace_append hprefix tailTrace_118949
  have hstable : (prefixWord ++ tailWord_118949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118949).length < 2 ^ (prefixWord ++ tailWord_118949).sum := by decide
  have hdescent : baseEnd_118949 < baseStart_118949 := by decide
  rcases family_descends (prefixWord ++ tailWord_118949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119026 : List Nat := [3, 2, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_119026 : Nat := 118140960795 + 119026 * 2 ^ 59
def prefixEnd_119026 : Nat := 4983230072969 + 3 ^ 40 * 119026 * 2
def baseEnd_119026 : Nat := 40745032254771029285077

theorem tailTrace_119026 : CollatzResearch.WordTrace tailWord_119026 prefixEnd_119026 40745032254771029285077 := by
  unfold tailWord_119026
  simp only [CollatzResearch.WordTrace]
  refine ⟨1085308716699151216878233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2894156577864403245008621 1085308716699151216878233)
  ·
    refine ⟨813981537524363412658675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1085308716699151216878233 813981537524363412658675)
    ·
      refine ⟨1220972306286545118988013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 813981537524363412658675 1220972306286545118988013)
      ·
        refine ⟨457864614857454419620505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1220972306286545118988013 457864614857454419620505)
        ·
          refine ⟨343398461143090814715379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457864614857454419620505 343398461143090814715379)
          ·
            refine ⟨515097691714636222073069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343398461143090814715379 515097691714636222073069)
            ·
              refine ⟨193161634392988583277401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 515097691714636222073069 193161634392988583277401)
              ·
                refine ⟨144871225794741437458051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193161634392988583277401 144871225794741437458051)
                ·
                  refine ⟨217306838692112156187077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144871225794741437458051 217306838692112156187077)
                  ·
                    refine ⟨40745032254771029285077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 217306838692112156187077 40745032254771029285077)
                    ·
                      rfl

theorem cell22_119026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_119026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119026 prefixEnd_119026 := by exact prefixLift 119026
  have htrace : WordTrace (prefixWord ++ tailWord_119026) baseStart_119026 baseEnd_119026 := by
    simpa [prefixWord, tailWord_119026, baseEnd_119026] using wordTrace_append hprefix tailTrace_119026
  have hstable : (prefixWord ++ tailWord_119026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119026).length < 2 ^ (prefixWord ++ tailWord_119026).sum := by decide
  have hdescent : baseEnd_119026 < baseStart_119026 := by decide
  rcases family_descends (prefixWord ++ tailWord_119026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119037 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_119037 : Nat := 118140960795 + 119037 * 2 ^ 59
def prefixEnd_119037 : Nat := 4983230072969 + 3 ^ 40 * 119037 * 2
def baseEnd_119037 : Nat := 40748797779570667260043

theorem tailTrace_119037 : CollatzResearch.WordTrace tailWord_119037 prefixEnd_119037 40748797779570667260043 := by
  unfold tailWord_119037
  simp only [CollatzResearch.WordTrace]
  refine ⟨4341636069756753746163365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2894424046504502497442243 4341636069756753746163365)
  ·
    refine ⟨814056763079391327405631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4341636069756753746163365 814056763079391327405631)
    ·
      refine ⟨1221085144619086991108447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 814056763079391327405631 1221085144619086991108447)
      ·
        refine ⟨1831627716928630486662671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1221085144619086991108447 1831627716928630486662671)
        ·
          refine ⟨2747441575392945729994007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1831627716928630486662671 2747441575392945729994007)
          ·
            refine ⟨4121162363089418594991011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747441575392945729994007 4121162363089418594991011)
            ·
              refine ⟨6181743544634127892486517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121162363089418594991011 6181743544634127892486517)
              ·
                refine ⟨579538457309449489920611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6181743544634127892486517 579538457309449489920611)
                ·
                  refine ⟨869307685964174234880917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 579538457309449489920611 869307685964174234880917)
                  ·
                    refine ⟨40748797779570667260043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 869307685964174234880917 40748797779570667260043)
                    ·
                      rfl

theorem cell22_119037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_119037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119037 prefixEnd_119037 := by exact prefixLift 119037
  have htrace : WordTrace (prefixWord ++ tailWord_119037) baseStart_119037 baseEnd_119037 := by
    simpa [prefixWord, tailWord_119037, baseEnd_119037] using wordTrace_append hprefix tailTrace_119037
  have hstable : (prefixWord ++ tailWord_119037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119037).length < 2 ^ (prefixWord ++ tailWord_119037).sum := by decide
  have hdescent : baseEnd_119037 < baseStart_119037 := by decide
  rcases family_descends (prefixWord ++ tailWord_119037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119054 : List Nat := [4, 1, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_119054 : Nat := 118140960795 + 119054 * 2 ^ 59
def prefixEnd_119054 : Nat := 4983230072969 + 3 ^ 40 * 119054 * 2
def baseEnd_119054 : Nat := 40754617226988289584991

theorem tailTrace_119054 : CollatzResearch.WordTrace tailWord_119054 prefixEnd_119054 40754617226988289584991 := by
  unfold tailWord_119054
  simp only [CollatzResearch.WordTrace]
  refine ⟨542782013836895706191527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2894837407130110433021477 542782013836895706191527)
  ·
    refine ⟨814173020755343559287291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 542782013836895706191527 814173020755343559287291)
    ·
      refine ⟨1221259531133015338930937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 814173020755343559287291 1221259531133015338930937)
      ·
        refine ⟨915944648349761504198203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1221259531133015338930937 915944648349761504198203)
        ·
          refine ⟨1373916972524642256297305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915944648349761504198203 1373916972524642256297305)
          ·
            refine ⟨1030437729393481692222979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1373916972524642256297305 1030437729393481692222979)
            ·
              refine ⟨1545656594090222538334469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030437729393481692222979 1545656594090222538334469)
              ·
                refine ⟨289810611391916725937713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1545656594090222538334469 289810611391916725937713)
                ·
                  refine ⟨217357958543937544453285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289810611391916725937713 217357958543937544453285)
                  ·
                    refine ⟨40754617226988289584991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 217357958543937544453285 40754617226988289584991)
                    ·
                      rfl

theorem cell22_119054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_119054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119054 prefixEnd_119054 := by exact prefixLift 119054
  have htrace : WordTrace (prefixWord ++ tailWord_119054) baseStart_119054 baseEnd_119054 := by
    simpa [prefixWord, tailWord_119054, baseEnd_119054] using wordTrace_append hprefix tailTrace_119054
  have hstable : (prefixWord ++ tailWord_119054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119054).length < 2 ^ (prefixWord ++ tailWord_119054).sum := by decide
  have hdescent : baseEnd_119054 < baseStart_119054 := by decide
  rcases family_descends (prefixWord ++ tailWord_119054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119084 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 5, 3]
def baseStart_119084 : Nat := 118140960795 + 119084 * 2 ^ 59
def prefixEnd_119084 : Nat := 4983230072969 + 3 ^ 40 * 119084 * 2
def baseEnd_119084 : Nat := 40764886840078211334899

theorem tailTrace_119084 : CollatzResearch.WordTrace tailWord_119084 prefixEnd_119084 40764886840078211334899 := by
  unfold tailWord_119084
  simp only [CollatzResearch.WordTrace]
  refine ⟨2171675150293240386562153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2895566867057653848749537 2171675150293240386562153)
  ·
    refine ⟨1628756362719930289921615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2171675150293240386562153 1628756362719930289921615)
    ·
      refine ⟨2443134544079895434882423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1628756362719930289921615 2443134544079895434882423)
      ·
        refine ⟨3664701816119843152323635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2443134544079895434882423 3664701816119843152323635)
        ·
          refine ⟨5497052724179764728485453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3664701816119843152323635 5497052724179764728485453)
          ·
            refine ⟨2061394771567411773182045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5497052724179764728485453 2061394771567411773182045)
            ·
              refine ⟨773023039337779414943267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2061394771567411773182045 773023039337779414943267)
              ·
                refine ⟨1159534559006669122414901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773023039337779414943267 1159534559006669122414901)
                ·
                  refine ⟨108706364906875230226397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1159534559006669122414901 108706364906875230226397)
                  ·
                    refine ⟨40764886840078211334899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108706364906875230226397 40764886840078211334899)
                    ·
                      rfl

theorem cell22_119084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_119084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119084 prefixEnd_119084 := by exact prefixLift 119084
  have htrace : WordTrace (prefixWord ++ tailWord_119084) baseStart_119084 baseEnd_119084 := by
    simpa [prefixWord, tailWord_119084, baseEnd_119084] using wordTrace_append hprefix tailTrace_119084
  have hstable : (prefixWord ++ tailWord_119084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119084).length < 2 ^ (prefixWord ++ tailWord_119084).sum := by decide
  have hdescent : baseEnd_119084 < baseStart_119084 := by decide
  rcases family_descends (prefixWord ++ tailWord_119084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119189 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 6, 4]
def baseStart_119189 : Nat := 118140960795 + 119189 * 2 ^ 59
def prefixEnd_119189 : Nat := 4983230072969 + 3 ^ 40 * 119189 * 2
def baseEnd_119189 : Nat := 40800830485892937459577

theorem tailTrace_119189 : CollatzResearch.WordTrace tailWord_119189 prefixEnd_119189 40800830485892937459577 := by
  unfold tailWord_119189
  simp only [CollatzResearch.WordTrace]
  refine ⟨4347179965206083705696621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2898119976804055803797747 4347179965206083705696621)
  ·
    refine ⟨1630192486952281389636233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4347179965206083705696621 1630192486952281389636233)
    ·
      refine ⟨1222644365214211042227175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1630192486952281389636233 1222644365214211042227175)
      ·
        refine ⟨1833966547821316563340763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1222644365214211042227175 1833966547821316563340763)
        ·
          refine ⟨2750949821731974845011145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1833966547821316563340763 2750949821731974845011145)
          ·
            refine ⟨2063212366298981133758359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2750949821731974845011145 2063212366298981133758359)
            ·
              refine ⟨3094818549448471700637539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2063212366298981133758359 3094818549448471700637539)
              ·
                refine ⟨4642227824172707550956309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3094818549448471700637539 4642227824172707550956309)
                ·
                  refine ⟨217604429258095666451077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4642227824172707550956309 217604429258095666451077)
                  ·
                    refine ⟨40800830485892937459577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 217604429258095666451077 40800830485892937459577)
                    ·
                      rfl

theorem cell22_119189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_119189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119189 prefixEnd_119189 := by exact prefixLift 119189
  have htrace : WordTrace (prefixWord ++ tailWord_119189) baseStart_119189 baseEnd_119189 := by
    simpa [prefixWord, tailWord_119189, baseEnd_119189] using wordTrace_append hprefix tailTrace_119189
  have hstable : (prefixWord ++ tailWord_119189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119189).length < 2 ^ (prefixWord ++ tailWord_119189).sum := by decide
  have hdescent : baseEnd_119189 < baseStart_119189 := by decide
  rcases family_descends (prefixWord ++ tailWord_119189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119204 : List Nat := [2, 3, 1, 2, 1, 1, 4, 8]
def baseStart_119204 : Nat := 118140960795 + 119204 * 2 ^ 59
def prefixEnd_119204 : Nat := 4983230072969 + 3 ^ 40 * 119204 * 2
def baseEnd_119204 : Nat := 4533996143604210926059

theorem tailTrace_119204 : CollatzResearch.WordTrace tailWord_119204 prefixEnd_119204 4533996143604210926059 := by
  unfold tailWord_119204
  simp only [CollatzResearch.WordTrace]
  refine ⟨2173863530075870633746333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2898484706767827511661777 2173863530075870633746333)
  ·
    refine ⟨815198823778451487654875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2173863530075870633746333 815198823778451487654875)
    ·
      refine ⟨1222798235667677231482313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 815198823778451487654875 1222798235667677231482313)
      ·
        refine ⟨917098676750757923611735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1222798235667677231482313 917098676750757923611735)
        ·
          refine ⟨1375648015126136885417603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 917098676750757923611735 1375648015126136885417603)
          ·
            refine ⟨2063472022689205328126405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1375648015126136885417603 2063472022689205328126405)
            ·
              refine ⟨386901004254225999023701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2063472022689205328126405 386901004254225999023701)
              ·
                refine ⟨4533996143604210926059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 386901004254225999023701 4533996143604210926059)
                ·
                  rfl

theorem cell22_119204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 8].length) (baseStart_119204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119204 prefixEnd_119204 := by exact prefixLift 119204
  have htrace : WordTrace (prefixWord ++ tailWord_119204) baseStart_119204 baseEnd_119204 := by
    simpa [prefixWord, tailWord_119204, baseEnd_119204] using wordTrace_append hprefix tailTrace_119204
  have hstable : (prefixWord ++ tailWord_119204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119204).length < 2 ^ (prefixWord ++ tailWord_119204).sum := by decide
  have hdescent : baseEnd_119204 < baseStart_119204 := by decide
  rcases family_descends (prefixWord ++ tailWord_119204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119208 : List Nat := [2, 1, 6, 1, 1, 2, 1, 2, 1, 5]
def baseStart_119208 : Nat := 118140960795 + 119208 * 2 ^ 59
def prefixEnd_119208 : Nat := 4983230072969 + 3 ^ 40 * 119208 * 2
def baseEnd_119208 : Nat := 40807334574183221234519

theorem tailTrace_119208 : CollatzResearch.WordTrace tailWord_119208 prefixEnd_119208 40807334574183221234519 := by
  unfold tailWord_119208
  simp only [CollatzResearch.WordTrace]
  refine ⟨2173936476068624975319139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2898581968091499967092185 2173936476068624975319139)
  ·
    refine ⟨3260904714102937462978709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2173936476068624975319139 3260904714102937462978709)
    ·
      refine ⟨152854908473575193577127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3260904714102937462978709 152854908473575193577127)
      ·
        refine ⟨229282362710362790365691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152854908473575193577127 229282362710362790365691)
        ·
          refine ⟨343923544065544185548537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229282362710362790365691 343923544065544185548537)
          ·
            refine ⟨257942658049158139161403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343923544065544185548537 257942658049158139161403)
            ·
              refine ⟨386913987073737208742105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257942658049158139161403 386913987073737208742105)
              ·
                refine ⟨290185490305302906556579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386913987073737208742105 290185490305302906556579)
                ·
                  refine ⟨435278235457954359834869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290185490305302906556579 435278235457954359834869)
                  ·
                    refine ⟨40807334574183221234519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 435278235457954359834869 40807334574183221234519)
                    ·
                      rfl

theorem cell22_119208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_119208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119208 prefixEnd_119208 := by exact prefixLift 119208
  have htrace : WordTrace (prefixWord ++ tailWord_119208) baseStart_119208 baseEnd_119208 := by
    simpa [prefixWord, tailWord_119208, baseEnd_119208] using wordTrace_append hprefix tailTrace_119208
  have hstable : (prefixWord ++ tailWord_119208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119208).length < 2 ^ (prefixWord ++ tailWord_119208).sum := by decide
  have hdescent : baseEnd_119208 < baseStart_119208 := by decide
  rcases family_descends (prefixWord ++ tailWord_119208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119221 : List Nat := [1, 3, 3, 2, 4, 9]
def baseStart_119221 : Nat := 118140960795 + 119221 * 2 ^ 59
def prefixEnd_119221 : Nat := 4983230072969 + 3 ^ 40 * 119221 * 2
def baseEnd_119221 : Nat := 503849194319203958759

theorem tailTrace_119221 : CollatzResearch.WordTrace tailWord_119221 prefixEnd_119221 503849194319203958759 := by
  unfold tailWord_119221
  simp only [CollatzResearch.WordTrace]
  refine ⟨4348347101090153170861517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2898898067393435447241011 4348347101090153170861517)
  ·
    refine ⟨1630630162908807439073069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4348347101090153170861517 1630630162908807439073069)
    ·
      refine ⟨611486311090802789652401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1630630162908807439073069 611486311090802789652401)
      ·
        refine ⟨458614733318102092239301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 611486311090802789652401 458614733318102092239301)
        ·
          refine ⟨85990262497144142294869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 458614733318102092239301 85990262497144142294869)
          ·
            refine ⟨503849194319203958759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 85990262497144142294869 503849194319203958759)
            ·
              rfl

theorem cell22_119221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 9].length) (baseStart_119221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119221 prefixEnd_119221 := by exact prefixLift 119221
  have htrace : WordTrace (prefixWord ++ tailWord_119221) baseStart_119221 baseEnd_119221 := by
    simpa [prefixWord, tailWord_119221, baseEnd_119221] using wordTrace_append hprefix tailTrace_119221
  have hstable : (prefixWord ++ tailWord_119221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119221).length < 2 ^ (prefixWord ++ tailWord_119221).sum := by decide
  have hdescent : baseEnd_119221 < baseStart_119221 := by decide
  rcases family_descends (prefixWord ++ tailWord_119221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119253 : List Nat := [1, 3, 2, 3, 1, 3, 1, 2, 3, 3]
def baseStart_119253 : Nat := 118140960795 + 119253 * 2 ^ 59
def prefixEnd_119253 : Nat := 4983230072969 + 3 ^ 40 * 119253 * 2
def baseEnd_119253 : Nat := 40822738993818103859381

theorem tailTrace_119253 : CollatzResearch.WordTrace tailWord_119253 prefixEnd_119253 40822738993818103859381 := by
  unfold tailWord_119253
  simp only [CollatzResearch.WordTrace]
  refine ⟨4349514236974222636026413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2899676157982815090684275 4349514236974222636026413)
  ·
    refine ⟨1631067838865333488509905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4349514236974222636026413 1631067838865333488509905)
    ·
      refine ⟨1223300879149000116382429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1631067838865333488509905 1223300879149000116382429)
      ·
        refine ⟨458737829680875043643411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1223300879149000116382429 458737829680875043643411)
        ·
          refine ⟨688106744521312565465117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458737829680875043643411 688106744521312565465117)
          ·
            refine ⟨258040029195492212049419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 688106744521312565465117 258040029195492212049419)
            ·
              refine ⟨387060043793238318074129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258040029195492212049419 387060043793238318074129)
              ·
                refine ⟨290295032844928738555597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387060043793238318074129 290295032844928738555597)
                ·
                  refine ⟨108860637316848276958349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290295032844928738555597 108860637316848276958349)
                  ·
                    refine ⟨40822738993818103859381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108860637316848276958349 40822738993818103859381)
                    ·
                      rfl

theorem cell22_119253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_119253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119253 prefixEnd_119253 := by exact prefixLift 119253
  have htrace : WordTrace (prefixWord ++ tailWord_119253) baseStart_119253 baseEnd_119253 := by
    simpa [prefixWord, tailWord_119253, baseEnd_119253] using wordTrace_append hprefix tailTrace_119253
  have hstable : (prefixWord ++ tailWord_119253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119253).length < 2 ^ (prefixWord ++ tailWord_119253).sum := by decide
  have hdescent : baseEnd_119253 < baseStart_119253 := by decide
  rcases family_descends (prefixWord ++ tailWord_119253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119264 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 1, 7]
def baseStart_119264 : Nat := 118140960795 + 119264 * 2 ^ 59
def prefixEnd_119264 : Nat := 4983230072969 + 3 ^ 40 * 119264 * 2
def baseEnd_119264 : Nat := 40826504518617741834347

theorem tailTrace_119264 : CollatzResearch.WordTrace tailWord_119264 prefixEnd_119264 40826504518617741834347 := by
  unfold tailWord_119264
  simp only [CollatzResearch.WordTrace]
  refine ⟨2174957719967185757338423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2899943626622914343117897 2174957719967185757338423)
  ·
    refine ⟨3262436579950778636007635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2174957719967185757338423 3262436579950778636007635)
    ·
      refine ⟨4893654869926167954011453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3262436579950778636007635 4893654869926167954011453)
      ·
        refine ⟨1835120576222312982754295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4893654869926167954011453 1835120576222312982754295)
        ·
          refine ⟨2752680864333469474131443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1835120576222312982754295 2752680864333469474131443)
          ·
            refine ⟨4129021296500204211197165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2752680864333469474131443 4129021296500204211197165)
            ·
              refine ⟨1548382986187576579198937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4129021296500204211197165 1548382986187576579198937)
              ·
                refine ⟨1161287239640682434399203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548382986187576579198937 1161287239640682434399203)
                ·
                  refine ⟨1741930859461023651598805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1161287239640682434399203 1741930859461023651598805)
                  ·
                    refine ⟨40826504518617741834347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1741930859461023651598805 40826504518617741834347)
                    ·
                      rfl

theorem cell22_119264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_119264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119264 prefixEnd_119264 := by exact prefixLift 119264
  have htrace : WordTrace (prefixWord ++ tailWord_119264) baseStart_119264 baseEnd_119264 := by
    simpa [prefixWord, tailWord_119264, baseEnd_119264] using wordTrace_append hprefix tailTrace_119264
  have hstable : (prefixWord ++ tailWord_119264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119264).length < 2 ^ (prefixWord ++ tailWord_119264).sum := by decide
  have hdescent : baseEnd_119264 < baseStart_119264 := by decide
  rcases family_descends (prefixWord ++ tailWord_119264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119300 : List Nat := [2, 3, 2, 3, 1, 2, 3, 1, 5]
def baseStart_119300 : Nat := 118140960795 + 119300 * 2 ^ 59
def prefixEnd_119300 : Nat := 4983230072969 + 3 ^ 40 * 119300 * 2
def baseEnd_119300 : Nat := 13612942684775215978079

theorem tailTrace_119300 : CollatzResearch.WordTrace tailWord_119300 prefixEnd_119300 13612942684775215978079 := by
  unfold tailWord_119300
  simp only [CollatzResearch.WordTrace]
  refine ⟨2175614233901974831493677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2900818978535966441991569 2175614233901974831493677)
  ·
    refine ⟨815855337713240561810129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2175614233901974831493677 815855337713240561810129)
    ·
      refine ⟨611891503284930421357597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 815855337713240561810129 611891503284930421357597)
      ·
        refine ⟨229459313731848908009099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 611891503284930421357597 229459313731848908009099)
        ·
          refine ⟨344188970597773362013649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229459313731848908009099 344188970597773362013649)
          ·
            refine ⟨258141727948330021510237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344188970597773362013649 258141727948330021510237)
            ·
              refine ⟨96803147980623758066339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258141727948330021510237 96803147980623758066339)
              ·
                refine ⟨145204721970935637099509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96803147980623758066339 145204721970935637099509)
                ·
                  refine ⟨13612942684775215978079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145204721970935637099509 13612942684775215978079)
                  ·
                    rfl

theorem cell22_119300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_119300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119300 prefixEnd_119300 := by exact prefixLift 119300
  have htrace : WordTrace (prefixWord ++ tailWord_119300) baseStart_119300 baseEnd_119300 := by
    simpa [prefixWord, tailWord_119300, baseEnd_119300] using wordTrace_append hprefix tailTrace_119300
  have hstable : (prefixWord ++ tailWord_119300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119300).length < 2 ^ (prefixWord ++ tailWord_119300).sum := by decide
  have hdescent : baseEnd_119300 < baseStart_119300 := by decide
  rcases family_descends (prefixWord ++ tailWord_119300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119356 : List Nat := [2, 2, 2, 2, 3, 1, 1, 9]
def baseStart_119356 : Nat := 118140960795 + 119356 * 2 ^ 59
def prefixEnd_119356 : Nat := 4983230072969 + 3 ^ 40 * 119356 * 2
def baseEnd_119356 : Nat := 4539777555417796503785

theorem tailTrace_119356 : CollatzResearch.WordTrace tailWord_119356 prefixEnd_119356 4539777555417796503785 := by
  unfold tailWord_119356
  simp only [CollatzResearch.WordTrace]
  refine ⟨2176635477800535613512961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2902180637067380818017281 2176635477800535613512961)
  ·
    refine ⟨1632476608350401710134721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2176635477800535613512961 1632476608350401710134721)
    ·
      refine ⟨1224357456262801282601041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1632476608350401710134721 1224357456262801282601041)
      ·
        refine ⟨918268092197100961950781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1224357456262801282601041 918268092197100961950781)
        ·
          refine ⟨344350534573912860731543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 918268092197100961950781 344350534573912860731543)
          ·
            refine ⟨516525801860869291097315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344350534573912860731543 516525801860869291097315)
            ·
              refine ⟨774788702791303936645973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516525801860869291097315 774788702791303936645973)
              ·
                refine ⟨4539777555417796503785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 774788702791303936645973 4539777555417796503785)
                ·
                  rfl

theorem cell22_119356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 9].length) (baseStart_119356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119356 prefixEnd_119356 := by exact prefixLift 119356
  have htrace : WordTrace (prefixWord ++ tailWord_119356) baseStart_119356 baseEnd_119356 := by
    simpa [prefixWord, tailWord_119356, baseEnd_119356] using wordTrace_append hprefix tailTrace_119356
  have hstable : (prefixWord ++ tailWord_119356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119356).length < 2 ^ (prefixWord ++ tailWord_119356).sum := by decide
  have hdescent : baseEnd_119356 < baseStart_119356 := by decide
  rcases family_descends (prefixWord ++ tailWord_119356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119360 : List Nat := [2, 1, 1, 2, 2, 2, 6, 1, 2, 3]
def baseStart_119360 : Nat := 118140960795 + 119360 * 2 ^ 59
def prefixEnd_119360 : Nat := 4983230072969 + 3 ^ 40 * 119360 * 2
def baseEnd_119360 : Nat := 40859367280505491434053

theorem tailTrace_119360 : CollatzResearch.WordTrace tailWord_119360 prefixEnd_119360 40859367280505491434053 := by
  unfold tailWord_119360
  simp only [CollatzResearch.WordTrace]
  refine ⟨2176708423793289955085767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2902277898391053273447689 2176708423793289955085767)
  ·
    refine ⟨3265062635689934932628651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2176708423793289955085767 3265062635689934932628651)
    ·
      refine ⟨4897593953534902398942977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3265062635689934932628651 4897593953534902398942977)
      ·
        refine ⟨3673195465151176799207233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4897593953534902398942977 3673195465151176799207233)
        ·
          refine ⟨2754896598863382599405425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3673195465151176799207233 2754896598863382599405425)
          ·
            refine ⟨2066172449147536949554069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2754896598863382599405425 2066172449147536949554069)
            ·
              refine ⟨96851833553790794510347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2066172449147536949554069 96851833553790794510347)
              ·
                refine ⟨145277750330686191765521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96851833553790794510347 145277750330686191765521)
                ·
                  refine ⟨108958312748014643824141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145277750330686191765521 108958312748014643824141)
                  ·
                    refine ⟨40859367280505491434053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108958312748014643824141 40859367280505491434053)
                    ·
                      rfl

theorem cell22_119360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 2, 3].length) (baseStart_119360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119360 prefixEnd_119360 := by exact prefixLift 119360
  have htrace : WordTrace (prefixWord ++ tailWord_119360) baseStart_119360 baseEnd_119360 := by
    simpa [prefixWord, tailWord_119360, baseEnd_119360] using wordTrace_append hprefix tailTrace_119360
  have hstable : (prefixWord ++ tailWord_119360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119360).length < 2 ^ (prefixWord ++ tailWord_119360).sum := by decide
  have hdescent : baseEnd_119360 < baseStart_119360 := by decide
  rcases family_descends (prefixWord ++ tailWord_119360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119373 : List Nat := [1, 6, 1, 1, 2, 1, 2, 8]
def baseStart_119373 : Nat := 118140960795 + 119373 * 2 ^ 59
def prefixEnd_119373 : Nat := 4983230072969 + 3 ^ 40 * 119373 * 2
def baseEnd_119373 : Nat := 4540424160686421206557

theorem tailTrace_119373 : CollatzResearch.WordTrace tailWord_119373 prefixEnd_119373 4540424160686421206557 := by
  unfold tailWord_119373
  simp only [CollatzResearch.WordTrace]
  refine ⟨4353890996539483130394773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2902593997692988753596515 4353890996539483130394773)
  ·
    refine ⟨204088640462788271737255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4353890996539483130394773 204088640462788271737255)
    ·
      refine ⟨306132960694182407605883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204088640462788271737255 306132960694182407605883)
      ·
        refine ⟨459199441041273611408825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306132960694182407605883 459199441041273611408825)
        ·
          refine ⟨344399580780955208556619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459199441041273611408825 344399580780955208556619)
          ·
            refine ⟨516599371171432812834929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344399580780955208556619 516599371171432812834929)
            ·
              refine ⟨387449528378574609626197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516599371171432812834929 387449528378574609626197)
              ·
                refine ⟨4540424160686421206557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 387449528378574609626197 4540424160686421206557)
                ·
                  rfl

theorem cell22_119373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 8].length) (baseStart_119373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119373 prefixEnd_119373 := by exact prefixLift 119373
  have htrace : WordTrace (prefixWord ++ tailWord_119373) baseStart_119373 baseEnd_119373 := by
    simpa [prefixWord, tailWord_119373, baseEnd_119373] using wordTrace_append hprefix tailTrace_119373
  have hstable : (prefixWord ++ tailWord_119373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119373).length < 2 ^ (prefixWord ++ tailWord_119373).sum := by decide
  have hdescent : baseEnd_119373 < baseStart_119373 := by decide
  rcases family_descends (prefixWord ++ tailWord_119373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119390 : List Nat := [4, 4, 1, 2, 11]
def baseStart_119390 : Nat := 118140960795 + 119390 * 2 ^ 59
def prefixEnd_119390 : Nat := 4983230072969 + 3 ^ 40 * 119390 * 2
def baseEnd_119390 : Nat := 168187806146483181827

theorem tailTrace_119390 : CollatzResearch.WordTrace tailWord_119390 prefixEnd_119390 168187806146483181827 := by
  unfold tailWord_119390
  simp only [CollatzResearch.WordTrace]
  refine ⟨544313879684736879220453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2903007358318596689175749 544313879684736879220453)
  ·
    refine ⟨102058852440888164853835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 544313879684736879220453 102058852440888164853835)
    ·
      refine ⟨153088278661332247280753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102058852440888164853835 153088278661332247280753)
      ·
        refine ⟨114816208995999185460565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153088278661332247280753 114816208995999185460565)
        ·
          refine ⟨168187806146483181827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 114816208995999185460565 168187806146483181827)
          ·
            rfl

theorem cell22_119390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 11].length) (baseStart_119390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119390 prefixEnd_119390 := by exact prefixLift 119390
  have htrace : WordTrace (prefixWord ++ tailWord_119390) baseStart_119390 baseEnd_119390 := by
    simpa [prefixWord, tailWord_119390, baseEnd_119390] using wordTrace_append hprefix tailTrace_119390
  have hstable : (prefixWord ++ tailWord_119390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119390).length < 2 ^ (prefixWord ++ tailWord_119390).sum := by decide
  have hdescent : baseEnd_119390 < baseStart_119390 := by decide
  rcases family_descends (prefixWord ++ tailWord_119390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119394 : List Nat := [3, 3, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_119394 : Nat := 118140960795 + 119394 * 2 ^ 59
def prefixEnd_119394 : Nat := 4983230072969 + 3 ^ 40 * 119394 * 2
def baseEnd_119394 : Nat := 40871006175340736083949

theorem tailTrace_119394 : CollatzResearch.WordTrace tailWord_119394 prefixEnd_119394 40871006175340736083949 := by
  unfold tailWord_119394
  simp only [CollatzResearch.WordTrace]
  refine ⟨1088664232365850929227309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2903104619642269144606157 1088664232365850929227309)
  ·
    refine ⟨408249087137194098460241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1088664232365850929227309 408249087137194098460241)
    ·
      refine ⟨306186815352895573845181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408249087137194098460241 306186815352895573845181)
      ·
        refine ⟨114820055757335840191943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306186815352895573845181 114820055757335840191943)
        ·
          refine ⟨172230083636003760287915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114820055757335840191943 172230083636003760287915)
          ·
            refine ⟨258345125454005640431873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172230083636003760287915 258345125454005640431873)
            ·
              refine ⟨193758844090504230323905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258345125454005640431873 193758844090504230323905)
              ·
                refine ⟨145319133067878172742929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193758844090504230323905 145319133067878172742929)
                ·
                  refine ⟨108989349800908629557197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145319133067878172742929 108989349800908629557197)
                  ·
                    refine ⟨40871006175340736083949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108989349800908629557197 40871006175340736083949)
                    ·
                      rfl

theorem cell22_119394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_119394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119394 prefixEnd_119394 := by exact prefixLift 119394
  have htrace : WordTrace (prefixWord ++ tailWord_119394) baseStart_119394 baseEnd_119394 := by
    simpa [prefixWord, tailWord_119394, baseEnd_119394] using wordTrace_append hprefix tailTrace_119394
  have hstable : (prefixWord ++ tailWord_119394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119394).length < 2 ^ (prefixWord ++ tailWord_119394).sum := by decide
  have hdescent : baseEnd_119394 < baseStart_119394 := by decide
  rcases family_descends (prefixWord ++ tailWord_119394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119416 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 2, 5]
def baseStart_119416 : Nat := 118140960795 + 119416 * 2 ^ 59
def prefixEnd_119416 : Nat := 4983230072969 + 3 ^ 40 * 119416 * 2
def baseEnd_119416 : Nat := 40878537224940012033881

theorem tailTrace_119416 : CollatzResearch.WordTrace tailWord_119416 prefixEnd_119416 40878537224940012033881 := by
  unfold tailWord_119416
  simp only [CollatzResearch.WordTrace]
  refine ⟨2177729667691850737105051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2903639556922467649473401 2177729667691850737105051)
  ·
    refine ⟨3266594501537776105657577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2177729667691850737105051 3266594501537776105657577)
    ·
      refine ⟨2449945876153332079243183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3266594501537776105657577 2449945876153332079243183)
      ·
        refine ⟨3674918814229998118864775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2449945876153332079243183 3674918814229998118864775)
        ·
          refine ⟨5512378221344997178297163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3674918814229998118864775 5512378221344997178297163)
          ·
            refine ⟨8268567332017495767445745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5512378221344997178297163 8268567332017495767445745)
            ·
              refine ⟨6201425499013121825584309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8268567332017495767445745 6201425499013121825584309)
              ·
                refine ⟨581383640532480171148529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6201425499013121825584309 581383640532480171148529)
                ·
                  refine ⟨436037730399360128361397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581383640532480171148529 436037730399360128361397)
                  ·
                    refine ⟨40878537224940012033881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 436037730399360128361397 40878537224940012033881)
                    ·
                      rfl

theorem cell22_119416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_119416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119416 prefixEnd_119416 := by exact prefixLift 119416
  have htrace : WordTrace (prefixWord ++ tailWord_119416) baseStart_119416 baseEnd_119416 := by
    simpa [prefixWord, tailWord_119416, baseEnd_119416] using wordTrace_append hprefix tailTrace_119416
  have hstable : (prefixWord ++ tailWord_119416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119416).length < 2 ^ (prefixWord ++ tailWord_119416).sum := by decide
  have hdescent : baseEnd_119416 < baseStart_119416 := by decide
  rcases family_descends (prefixWord ++ tailWord_119416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119426 : List Nat := [3, 4, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_119426 : Nat := 118140960795 + 119426 * 2 ^ 59
def prefixEnd_119426 : Nat := 4983230072969 + 3 ^ 40 * 119426 * 2
def baseEnd_119426 : Nat := 40881960429303319283851

theorem tailTrace_119426 : CollatzResearch.WordTrace tailWord_119426 prefixEnd_119426 40881960429303319283851 := by
  unfold tailWord_119426
  simp only [CollatzResearch.WordTrace]
  refine ⟨1088956016336868295518533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2903882710231648788049421 1088956016336868295518533)
  ·
    refine ⟨204179253063162805409725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1088956016336868295518533 204179253063162805409725)
    ·
      refine ⟨76567219898686052028647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204179253063162805409725 76567219898686052028647)
      ·
        refine ⟨114850829848029078042971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76567219898686052028647 114850829848029078042971)
        ·
          refine ⟨172276244772043617064457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114850829848029078042971 172276244772043617064457)
          ·
            refine ⟨129207183579032712798343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172276244772043617064457 129207183579032712798343)
            ·
              refine ⟨193810775368549069197515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129207183579032712798343 193810775368549069197515)
              ·
                refine ⟨290716163052823603796273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193810775368549069197515 290716163052823603796273)
                ·
                  refine ⟨218037122289617702847205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290716163052823603796273 218037122289617702847205)
                  ·
                    refine ⟨40881960429303319283851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 218037122289617702847205 40881960429303319283851)
                    ·
                      rfl

theorem cell22_119426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_119426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119426 prefixEnd_119426 := by exact prefixLift 119426
  have htrace : WordTrace (prefixWord ++ tailWord_119426) baseStart_119426 baseEnd_119426 := by
    simpa [prefixWord, tailWord_119426, baseEnd_119426] using wordTrace_append hprefix tailTrace_119426
  have hstable : (prefixWord ++ tailWord_119426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119426).length < 2 ^ (prefixWord ++ tailWord_119426).sum := by decide
  have hdescent : baseEnd_119426 < baseStart_119426 := by decide
  rcases family_descends (prefixWord ++ tailWord_119426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119675 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 5, 3]
def baseStart_119675 : Nat := 118140960795 + 119675 * 2 ^ 59
def prefixEnd_119675 : Nat := 4983230072969 + 3 ^ 40 * 119675 * 2
def baseEnd_119675 : Nat := 40967198217949669808087

theorem tailTrace_119675 : CollatzResearch.WordTrace tailWord_119675 prefixEnd_119675 40967198217949669808087 := by
  unfold tailWord_119675
  simp only [CollatzResearch.WordTrace]
  refine ⟨4364905841445388707888479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2909937227630259138592319 4364905841445388707888479)
  ·
    refine ⟨6547358762168083061832719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4364905841445388707888479 6547358762168083061832719)
    ·
      refine ⟨9821038143252124592749079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6547358762168083061832719 9821038143252124592749079)
      ·
        refine ⟨14731557214878186889123619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9821038143252124592749079 14731557214878186889123619)
        ·
          refine ⟨22097335822317280333685429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14731557214878186889123619 22097335822317280333685429)
          ·
            refine ⟨2071625233342245031283009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22097335822317280333685429 2071625233342245031283009)
            ·
              refine ⟨1553718925006683773462257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2071625233342245031283009 1553718925006683773462257)
              ·
                refine ⟨1165289193755012830096693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553718925006683773462257 1165289193755012830096693)
                ·
                  refine ⟨109245861914532452821565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1165289193755012830096693 109245861914532452821565)
                  ·
                    refine ⟨40967198217949669808087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109245861914532452821565 40967198217949669808087)
                    ·
                      rfl

theorem cell22_119675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 3].length) (baseStart_119675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119675 prefixEnd_119675 := by exact prefixLift 119675
  have htrace : WordTrace (prefixWord ++ tailWord_119675) baseStart_119675 baseEnd_119675 := by
    simpa [prefixWord, tailWord_119675, baseEnd_119675] using wordTrace_append hprefix tailTrace_119675
  have hstable : (prefixWord ++ tailWord_119675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119675).length < 2 ^ (prefixWord ++ tailWord_119675).sum := by decide
  have hdescent : baseEnd_119675 < baseStart_119675 := by decide
  rcases family_descends (prefixWord ++ tailWord_119675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119692 : List Nat := [2, 2, 1, 2, 1, 2, 5, 1, 3, 3]
def baseStart_119692 : Nat := 118140960795 + 119692 * 2 ^ 59
def prefixEnd_119692 : Nat := 4983230072969 + 3 ^ 40 * 119692 * 2
def baseEnd_119692 : Nat := 40973017665367292133035

theorem tailTrace_119692 : CollatzResearch.WordTrace tailWord_119692 prefixEnd_119692 40973017665367292133035 := by
  unfold tailWord_119692
  simp only [CollatzResearch.WordTrace]
  refine ⟨2182762941191900305628665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2910350588255867074171553 2182762941191900305628665)
  ·
    refine ⟨1637072205893925229221499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2182762941191900305628665 1637072205893925229221499)
    ·
      refine ⟨2455608308840887843832249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1637072205893925229221499 2455608308840887843832249)
      ·
        refine ⟨1841706231630665882874187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2455608308840887843832249 1841706231630665882874187)
        ·
          refine ⟨2762559347445998824311281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841706231630665882874187 2762559347445998824311281)
          ·
            refine ⟨2071919510584499118233461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2762559347445998824311281 2071919510584499118233461)
            ·
              refine ⟨194242454117296792334387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2071919510584499118233461 194242454117296792334387)
              ·
                refine ⟨291363681175945188501581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194242454117296792334387 291363681175945188501581)
                ·
                  refine ⟨109261380440979445688093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291363681175945188501581 109261380440979445688093)
                  ·
                    refine ⟨40973017665367292133035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109261380440979445688093 40973017665367292133035)
                    ·
                      rfl

theorem cell22_119692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_119692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119692 prefixEnd_119692 := by exact prefixLift 119692
  have htrace : WordTrace (prefixWord ++ tailWord_119692) baseStart_119692 baseEnd_119692 := by
    simpa [prefixWord, tailWord_119692, baseEnd_119692] using wordTrace_append hprefix tailTrace_119692
  have hstable : (prefixWord ++ tailWord_119692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119692).length < 2 ^ (prefixWord ++ tailWord_119692).sum := by decide
  have hdescent : baseEnd_119692 < baseStart_119692 := by decide
  rcases family_descends (prefixWord ++ tailWord_119692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119698 : List Nat := [3, 2, 3, 2, 2, 2, 2, 1, 2, 3]
def baseStart_119698 : Nat := 118140960795 + 119698 * 2 ^ 59
def prefixEnd_119698 : Nat := 4983230072969 + 3 ^ 40 * 119698 * 2
def baseEnd_119698 : Nat := 40975071587985276483017

theorem tailTrace_119698 : CollatzResearch.WordTrace tailWord_119698 prefixEnd_119698 40975071587985276483017 := by
  unfold tailWord_119698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1091436180090515908993937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2910496480241375757317165 1091436180090515908993937)
  ·
    refine ⟨818577135067886931745453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1091436180090515908993937 818577135067886931745453)
    ·
      refine ⟨306966425650457599404545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 818577135067886931745453 306966425650457599404545)
      ·
        refine ⟨230224819237843199553409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306966425650457599404545 230224819237843199553409)
        ·
          refine ⟨172668614428382399665057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230224819237843199553409 172668614428382399665057)
          ·
            refine ⟨129501460821286799748793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172668614428382399665057 129501460821286799748793)
            ·
              refine ⟨97126095615965099811595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129501460821286799748793 97126095615965099811595)
              ·
                refine ⟨145689143423947649717393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97126095615965099811595 145689143423947649717393)
                ·
                  refine ⟨109266857567960737288045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145689143423947649717393 109266857567960737288045)
                  ·
                    refine ⟨40975071587985276483017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109266857567960737288045 40975071587985276483017)
                    ·
                      rfl

theorem cell22_119698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_119698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119698 prefixEnd_119698 := by exact prefixLift 119698
  have htrace : WordTrace (prefixWord ++ tailWord_119698) baseStart_119698 baseEnd_119698 := by
    simpa [prefixWord, tailWord_119698, baseEnd_119698] using wordTrace_append hprefix tailTrace_119698
  have hstable : (prefixWord ++ tailWord_119698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119698).length < 2 ^ (prefixWord ++ tailWord_119698).sum := by decide
  have hdescent : baseEnd_119698 < baseStart_119698 := by decide
  rcases family_descends (prefixWord ++ tailWord_119698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119786 : List Nat := [3, 1, 3, 1, 2, 4, 2, 1, 1, 4]
def baseStart_119786 : Nat := 118140960795 + 119786 * 2 ^ 59
def prefixEnd_119786 : Nat := 4983230072969 + 3 ^ 40 * 119786 * 2
def baseEnd_119786 : Nat := 41005195786382380282747

theorem tailTrace_119786 : CollatzResearch.WordTrace tailWord_119786 prefixEnd_119786 41005195786382380282747 := by
  unfold tailWord_119786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1092238586010813666294803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2912636229362169776786141 1092238586010813666294803)
  ·
    refine ⟨1638357879016220499442205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1092238586010813666294803 1638357879016220499442205)
    ·
      refine ⟨614384204631082687290827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1638357879016220499442205 614384204631082687290827)
      ·
        refine ⟨921576306946624030936241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614384204631082687290827 921576306946624030936241)
        ·
          refine ⟨691182230209968023202181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 921576306946624030936241 691182230209968023202181)
          ·
            refine ⟨129596668164369004350409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 691182230209968023202181 129596668164369004350409)
            ·
              refine ⟨97197501123276753262807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129596668164369004350409 97197501123276753262807)
              ·
                refine ⟨145796251684915129894211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97197501123276753262807 145796251684915129894211)
                ·
                  refine ⟨218694377527372694841317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145796251684915129894211 218694377527372694841317)
                  ·
                    refine ⟨41005195786382380282747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 218694377527372694841317 41005195786382380282747)
                    ·
                      rfl

theorem cell22_119786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_119786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119786 prefixEnd_119786 := by exact prefixLift 119786
  have htrace : WordTrace (prefixWord ++ tailWord_119786) baseStart_119786 baseEnd_119786 := by
    simpa [prefixWord, tailWord_119786, baseEnd_119786] using wordTrace_append hprefix tailTrace_119786
  have hstable : (prefixWord ++ tailWord_119786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119786).length < 2 ^ (prefixWord ++ tailWord_119786).sum := by decide
  have hdescent : baseEnd_119786 < baseStart_119786 := by decide
  rcases family_descends (prefixWord ++ tailWord_119786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119816 : List Nat := [2, 1, 3, 2, 1, 4, 3, 1, 2, 3]
def baseStart_119816 : Nat := 118140960795 + 119816 * 2 ^ 59
def prefixEnd_119816 : Nat := 4983230072969 + 3 ^ 40 * 119816 * 2
def baseEnd_119816 : Nat := 41015465399472302032655

theorem tailTrace_119816 : CollatzResearch.WordTrace tailWord_119816 prefixEnd_119816 41015465399472302032655 := by
  unfold tailWord_119816
  simp only [CollatzResearch.WordTrace]
  refine ⟨2185024266967284894385651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2913365689289713192514201 2185024266967284894385651)
  ·
    refine ⟨3277536400450927341578477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2185024266967284894385651 3277536400450927341578477)
    ·
      refine ⟨1229076150169097753091929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3277536400450927341578477 1229076150169097753091929)
      ·
        refine ⟨921807112626823314818947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1229076150169097753091929 921807112626823314818947)
        ·
          refine ⟨1382710668940234972228421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 921807112626823314818947 1382710668940234972228421)
          ·
            refine ⟨259258250426294057292829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1382710668940234972228421 259258250426294057292829)
            ·
              refine ⟨97221843909860271484811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259258250426294057292829 97221843909860271484811)
              ·
                refine ⟨145832765864790407227217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97221843909860271484811 145832765864790407227217)
                ·
                  refine ⟨109374574398592805420413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145832765864790407227217 109374574398592805420413)
                  ·
                    refine ⟨41015465399472302032655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109374574398592805420413 41015465399472302032655)
                    ·
                      rfl

theorem cell22_119816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_119816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119816 prefixEnd_119816 := by exact prefixLift 119816
  have htrace : WordTrace (prefixWord ++ tailWord_119816) baseStart_119816 baseEnd_119816 := by
    simpa [prefixWord, tailWord_119816, baseEnd_119816] using wordTrace_append hprefix tailTrace_119816
  have hstable : (prefixWord ++ tailWord_119816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119816).length < 2 ^ (prefixWord ++ tailWord_119816).sum := by decide
  have hdescent : baseEnd_119816 < baseStart_119816 := by decide
  rcases family_descends (prefixWord ++ tailWord_119816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119825 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 2, 6]
def baseStart_119825 : Nat := 118140960795 + 119825 * 2 ^ 59
def prefixEnd_119825 : Nat := 4983230072969 + 3 ^ 40 * 119825 * 2
def baseEnd_119825 : Nat := 41018546283399278557627

theorem tailTrace_119825 : CollatzResearch.WordTrace tailWord_119825 prefixEnd_119825 41018546283399278557627 := by
  unfold tailWord_119825
  simp only [CollatzResearch.WordTrace]
  refine ⟨4370376790901964325848929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2913584527267976217232619 4370376790901964325848929)
  ·
    refine ⟨3277782593176473244386697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4370376790901964325848929 3277782593176473244386697)
    ·
      refine ⟨2458336944882354933290023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3277782593176473244386697 2458336944882354933290023)
      ·
        refine ⟨3687505417323532399935035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2458336944882354933290023 3687505417323532399935035)
        ·
          refine ⟨5531258125985298599902553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3687505417323532399935035 5531258125985298599902553)
          ·
            refine ⟨4148443594488973949926915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5531258125985298599902553 4148443594488973949926915)
            ·
              refine ⟨6222665391733460924890373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4148443594488973949926915 6222665391733460924890373)
              ·
                refine ⟨1166749760950023923416945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6222665391733460924890373 1166749760950023923416945)
                ·
                  refine ⟨875062320712517942562709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1166749760950023923416945 875062320712517942562709)
                  ·
                    refine ⟨41018546283399278557627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 875062320712517942562709 41018546283399278557627)
                    ·
                      rfl

theorem cell22_119825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_119825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119825 prefixEnd_119825 := by exact prefixLift 119825
  have htrace : WordTrace (prefixWord ++ tailWord_119825) baseStart_119825 baseEnd_119825 := by
    simpa [prefixWord, tailWord_119825, baseEnd_119825] using wordTrace_append hprefix tailTrace_119825
  have hstable : (prefixWord ++ tailWord_119825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119825).length < 2 ^ (prefixWord ++ tailWord_119825).sum := by decide
  have hdescent : baseEnd_119825 < baseStart_119825 := by decide
  rcases family_descends (prefixWord ++ tailWord_119825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119829 : List Nat := [1, 3, 2, 1, 4, 3, 2, 6]
def baseStart_119829 : Nat := 118140960795 + 119829 * 2 ^ 59
def prefixEnd_119829 : Nat := 4983230072969 + 3 ^ 40 * 119829 * 2
def baseEnd_119829 : Nat := 4557768396127177939735

theorem tailTrace_119829 : CollatzResearch.WordTrace tailWord_119829 prefixEnd_119829 4557768396127177939735 := by
  unfold tailWord_119829
  simp only [CollatzResearch.WordTrace]
  refine ⟨4370522682887473008994541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2913681788591648672663027 4370522682887473008994541)
  ·
    refine ⟨1638946006082802378372953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4370522682887473008994541 1638946006082802378372953)
    ·
      refine ⟨1229209504562101783779715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1638946006082802378372953 1229209504562101783779715)
      ·
        refine ⟨1843814256843152675669573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1229209504562101783779715 1843814256843152675669573)
        ·
          refine ⟨345715173158091126688045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1843814256843152675669573 345715173158091126688045)
          ·
            refine ⟨129643189934284172508017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345715173158091126688045 129643189934284172508017)
            ·
              refine ⟨97232392450713129381013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129643189934284172508017 97232392450713129381013)
              ·
                refine ⟨4557768396127177939735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97232392450713129381013 4557768396127177939735)
                ·
                  rfl

theorem cell22_119829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 6].length) (baseStart_119829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119829 prefixEnd_119829 := by exact prefixLift 119829
  have htrace : WordTrace (prefixWord ++ tailWord_119829) baseStart_119829 baseEnd_119829 := by
    simpa [prefixWord, tailWord_119829, baseEnd_119829] using wordTrace_append hprefix tailTrace_119829
  have hstable : (prefixWord ++ tailWord_119829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119829).length < 2 ^ (prefixWord ++ tailWord_119829).sum := by decide
  have hdescent : baseEnd_119829 < baseStart_119829 := by decide
  rcases family_descends (prefixWord ++ tailWord_119829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119857 : List Nat := [1, 2, 2, 3, 1, 2, 2, 4, 5]
def baseStart_119857 : Nat := 118140960795 + 119857 * 2 ^ 59
def prefixEnd_119857 : Nat := 4983230072969 + 3 ^ 40 * 119857 * 2
def baseEnd_119857 : Nat := 13676500179120620585843

theorem tailTrace_119857 : CollatzResearch.WordTrace tailWord_119857 prefixEnd_119857 13676500179120620585843 := by
  unfold tailWord_119857
  simp only [CollatzResearch.WordTrace]
  refine ⟨4371543926786033791013825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2914362617857355860675883 4371543926786033791013825)
  ·
    refine ⟨3278657945089525343260369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4371543926786033791013825 3278657945089525343260369)
    ·
      refine ⟨2458993458817144007445277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3278657945089525343260369 2458993458817144007445277)
      ·
        refine ⟨922122547056429002791979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2458993458817144007445277 922122547056429002791979)
        ·
          refine ⟨1383183820584643504187969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 922122547056429002791979 1383183820584643504187969)
          ·
            refine ⟨1037387865438482628140977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1383183820584643504187969 1037387865438482628140977)
            ·
              refine ⟨778040899078861971105733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1037387865438482628140977 778040899078861971105733)
              ·
                refine ⟨145882668577286619582325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 778040899078861971105733 145882668577286619582325)
                ·
                  refine ⟨13676500179120620585843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145882668577286619582325 13676500179120620585843)
                  ·
                    rfl

theorem cell22_119857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 5].length) (baseStart_119857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119857 prefixEnd_119857 := by exact prefixLift 119857
  have htrace : WordTrace (prefixWord ++ tailWord_119857) baseStart_119857 baseEnd_119857 := by
    simpa [prefixWord, tailWord_119857, baseEnd_119857] using wordTrace_append hprefix tailTrace_119857
  have hstable : (prefixWord ++ tailWord_119857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119857).length < 2 ^ (prefixWord ++ tailWord_119857).sum := by decide
  have hdescent : baseEnd_119857 < baseStart_119857 := by decide
  rcases family_descends (prefixWord ++ tailWord_119857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119912 : List Nat := [2, 1, 4, 4, 1, 2, 2, 2, 1, 3]
def baseStart_119912 : Nat := 118140960795 + 119912 * 2 ^ 59
def prefixEnd_119912 : Nat := 4983230072969 + 3 ^ 40 * 119912 * 2
def baseEnd_119912 : Nat := 41048328161360051632361

theorem tailTrace_119912 : CollatzResearch.WordTrace tailWord_119912 prefixEnd_119912 41048328161360051632361 := by
  unfold tailWord_119912
  simp only [CollatzResearch.WordTrace]
  refine ⟨2186774970793389092132995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2915699961057852122843993 2186774970793389092132995)
  ·
    refine ⟨3280162456190083638199493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2186774970793389092132995 3280162456190083638199493)
    ·
      refine ⟨615030460535640682162405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3280162456190083638199493 615030460535640682162405)
      ·
        refine ⟨115318211350432627905451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 615030460535640682162405 115318211350432627905451)
        ·
          refine ⟨172977317025648941858177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115318211350432627905451 172977317025648941858177)
          ·
            refine ⟨129732987769236706393633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172977317025648941858177 129732987769236706393633)
            ·
              refine ⟨97299740826927529795225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129732987769236706393633 97299740826927529795225)
              ·
                refine ⟨72974805620195647346419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97299740826927529795225 72974805620195647346419)
                ·
                  refine ⟨109462208430293471019629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72974805620195647346419 109462208430293471019629)
                  ·
                    refine ⟨41048328161360051632361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109462208430293471019629 41048328161360051632361)
                    ·
                      rfl

theorem cell22_119912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_119912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119912 prefixEnd_119912 := by exact prefixLift 119912
  have htrace : WordTrace (prefixWord ++ tailWord_119912) baseStart_119912 baseEnd_119912 := by
    simpa [prefixWord, tailWord_119912, baseEnd_119912] using wordTrace_append hprefix tailTrace_119912
  have hstable : (prefixWord ++ tailWord_119912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119912).length < 2 ^ (prefixWord ++ tailWord_119912).sum := by decide
  have hdescent : baseEnd_119912 < baseStart_119912 := by decide
  rcases family_descends (prefixWord ++ tailWord_119912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119919 : List Nat := [1, 1, 2, 1, 3, 3, 3, 4, 4]
def baseStart_119919 : Nat := 118140960795 + 119919 * 2 ^ 59
def prefixEnd_119919 : Nat := 4983230072969 + 3 ^ 40 * 119919 * 2
def baseEnd_119919 : Nat := 13683574801471455569113

theorem tailTrace_119919 : CollatzResearch.WordTrace tailWord_119919 prefixEnd_119919 13683574801471455569113 := by
  unfold tailWord_119919
  simp only [CollatzResearch.WordTrace]
  refine ⟨4373805252561418379770811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2915870168374278919847207 4373805252561418379770811)
  ·
    refine ⟨6560707878842127569656217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4373805252561418379770811 6560707878842127569656217)
    ·
      refine ⟨4920530909131595677242163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6560707878842127569656217 4920530909131595677242163)
      ·
        refine ⟨7380796363697393515863245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4920530909131595677242163 7380796363697393515863245)
        ·
          refine ⟨2767798636386522568448717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7380796363697393515863245 2767798636386522568448717)
          ·
            refine ⟨1037924488644945963168269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2767798636386522568448717 1037924488644945963168269)
            ·
              refine ⟨389221683241854736188101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1037924488644945963168269 389221683241854736188101)
              ·
                refine ⟨72979065607847763035269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389221683241854736188101 72979065607847763035269)
                ·
                  refine ⟨13683574801471455569113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72979065607847763035269 13683574801471455569113)
                  ·
                    rfl

theorem cell22_119919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 4].length) (baseStart_119919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119919 prefixEnd_119919 := by exact prefixLift 119919
  have htrace : WordTrace (prefixWord ++ tailWord_119919) baseStart_119919 baseEnd_119919 := by
    simpa [prefixWord, tailWord_119919, baseEnd_119919] using wordTrace_append hprefix tailTrace_119919
  have hstable : (prefixWord ++ tailWord_119919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119919).length < 2 ^ (prefixWord ++ tailWord_119919).sum := by decide
  have hdescent : baseEnd_119919 < baseStart_119919 := by decide
  rcases family_descends (prefixWord ++ tailWord_119919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119932 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 1, 6]
def baseStart_119932 : Nat := 118140960795 + 119932 * 2 ^ 59
def prefixEnd_119932 : Nat := 4983230072969 + 3 ^ 40 * 119932 * 2
def baseEnd_119932 : Nat := 41055174570086666132299

theorem tailTrace_119932 : CollatzResearch.WordTrace tailWord_119932 prefixEnd_119932 41055174570086666132299 := by
  unfold tailWord_119932
  simp only [CollatzResearch.WordTrace]
  refine ⟨2187139700757160799997025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2916186267676214399996033 2187139700757160799997025)
  ·
    refine ⟨1640354775567870599997769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2187139700757160799997025 1640354775567870599997769)
    ·
      refine ⟨1230266081675902949998327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1640354775567870599997769 1230266081675902949998327)
      ·
        refine ⟨1845399122513854424997491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1230266081675902949998327 1845399122513854424997491)
        ·
          refine ⟨2768098683770781637496237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1845399122513854424997491 2768098683770781637496237)
          ·
            refine ⟨1038037006414043114061089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2768098683770781637496237 1038037006414043114061089)
            ·
              refine ⟨778527754810532335545817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038037006414043114061089 778527754810532335545817)
              ·
                refine ⟨583895816107899251659363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 778527754810532335545817 583895816107899251659363)
                ·
                  refine ⟨875843724161848877489045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583895816107899251659363 875843724161848877489045)
                  ·
                    refine ⟨41055174570086666132299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 875843724161848877489045 41055174570086666132299)
                    ·
                      rfl

theorem cell22_119932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_119932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119932 prefixEnd_119932 := by exact prefixLift 119932
  have htrace : WordTrace (prefixWord ++ tailWord_119932) baseStart_119932 baseEnd_119932 := by
    simpa [prefixWord, tailWord_119932, baseEnd_119932] using wordTrace_append hprefix tailTrace_119932
  have hstable : (prefixWord ++ tailWord_119932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119932).length < 2 ^ (prefixWord ++ tailWord_119932).sum := by decide
  have hdescent : baseEnd_119932 < baseStart_119932 := by decide
  rcases family_descends (prefixWord ++ tailWord_119932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119996 : List Nat := [2, 2, 2, 3, 2, 1, 2, 2, 3, 3]
def baseStart_119996 : Nat := 118140960795 + 119996 * 2 ^ 59
def prefixEnd_119996 : Nat := 4983230072969 + 3 ^ 40 * 119996 * 2
def baseEnd_119996 : Nat := 41077083078011832532103

theorem tailTrace_119996 : CollatzResearch.WordTrace tailWord_119996 prefixEnd_119996 41077083078011832532103 := by
  unfold tailWord_119996
  simp only [CollatzResearch.WordTrace]
  refine ⟨2188306836641230265161921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2917742448854973686882561 2188306836641230265161921)
  ·
    refine ⟨1641230127480922698871441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2188306836641230265161921 1641230127480922698871441)
    ·
      refine ⟨1230922595610692024153581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1641230127480922698871441 1230922595610692024153581)
      ·
        refine ⟨461595973354009509057593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1230922595610692024153581 461595973354009509057593)
        ·
          refine ⟨346196980015507131793195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461595973354009509057593 346196980015507131793195)
          ·
            refine ⟨519295470023260697689793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346196980015507131793195 519295470023260697689793)
            ·
              refine ⟨389471602517445523267345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519295470023260697689793 389471602517445523267345)
              ·
                refine ⟨292103701888084142450509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389471602517445523267345 292103701888084142450509)
                ·
                  refine ⟨109538888208031553418941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292103701888084142450509 109538888208031553418941)
                  ·
                    refine ⟨41077083078011832532103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109538888208031553418941 41077083078011832532103)
                    ·
                      rfl

theorem cell22_119996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_119996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_119996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_119996 prefixEnd_119996 := by exact prefixLift 119996
  have htrace : WordTrace (prefixWord ++ tailWord_119996) baseStart_119996 baseEnd_119996 := by
    simpa [prefixWord, tailWord_119996, baseEnd_119996] using wordTrace_append hprefix tailTrace_119996
  have hstable : (prefixWord ++ tailWord_119996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119996).length < 2 ^ (prefixWord ++ tailWord_119996).sum := by decide
  have hdescent : baseEnd_119996 < baseStart_119996 := by decide
  rcases family_descends (prefixWord ++ tailWord_119996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120007 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 1, 7]
def baseStart_120007 : Nat := 118140960795 + 120007 * 2 ^ 59
def prefixEnd_120007 : Nat := 4983230072969 + 3 ^ 40 * 120007 * 2
def baseEnd_120007 : Nat := 41080848602811470507069

theorem tailTrace_120007 : CollatzResearch.WordTrace tailWord_120007 prefixEnd_120007 41080848602811470507069 := by
  unfold tailWord_120007
  simp only [CollatzResearch.WordTrace]
  refine ⟨4377014876242609408974275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2918009917495072939316183 4377014876242609408974275)
  ·
    refine ⟨6565522314363914113461413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4377014876242609408974275 6565522314363914113461413)
    ·
      refine ⟨1231035433943233896274015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6565522314363914113461413 1231035433943233896274015)
      ·
        refine ⟨1846553150914850844411023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1231035433943233896274015 1846553150914850844411023)
        ·
          refine ⟨2769829726372276266616535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1846553150914850844411023 2769829726372276266616535)
          ·
            refine ⟨4154744589558414399924803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2769829726372276266616535 4154744589558414399924803)
            ·
              refine ⟨6232116884337621599887205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4154744589558414399924803 6232116884337621599887205)
              ·
                refine ⟨1168521915813304049978851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6232116884337621599887205 1168521915813304049978851)
                ·
                  refine ⟨1752782873719956074968277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1168521915813304049978851 1752782873719956074968277)
                  ·
                    refine ⟨41080848602811470507069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1752782873719956074968277 41080848602811470507069)
                    ·
                      rfl

theorem cell22_120007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_120007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120007 prefixEnd_120007 := by exact prefixLift 120007
  have htrace : WordTrace (prefixWord ++ tailWord_120007) baseStart_120007 baseEnd_120007 := by
    simpa [prefixWord, tailWord_120007, baseEnd_120007] using wordTrace_append hprefix tailTrace_120007
  have hstable : (prefixWord ++ tailWord_120007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120007).length < 2 ^ (prefixWord ++ tailWord_120007).sum := by decide
  have hdescent : baseEnd_120007 < baseStart_120007 := by decide
  rcases family_descends (prefixWord ++ tailWord_120007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120054 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_120054 : Nat := 118140960795 + 120054 * 2 ^ 59
def prefixEnd_120054 : Nat := 4983230072969 + 3 ^ 40 * 120054 * 2
def baseEnd_120054 : Nat := 13698979221106338193975

theorem tailTrace_120054 : CollatzResearch.WordTrace tailWord_120054 prefixEnd_120054 13698979221106338193975 := by
  unfold tailWord_120054
  simp only [CollatzResearch.WordTrace]
  refine ⟨273670569192021027245951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2919152738048224290623477 273670569192021027245951)
  ·
    refine ⟨410505853788031540868927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273670569192021027245951 410505853788031540868927)
    ·
      refine ⟨615758780682047311303391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410505853788031540868927 615758780682047311303391)
      ·
        refine ⟨923638171023070966955087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615758780682047311303391 923638171023070966955087)
        ·
          refine ⟨1385457256534606450432631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923638171023070966955087 1385457256534606450432631)
          ·
            refine ⟨2078185884801909675648947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385457256534606450432631 2078185884801909675648947)
            ·
              refine ⟨3117278827202864513473421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078185884801909675648947 3117278827202864513473421)
              ·
                refine ⟨1168979560201074192552533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3117278827202864513473421 1168979560201074192552533)
                ·
                  refine ⟨13698979221106338193975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1168979560201074192552533 13698979221106338193975)
                  ·
                    rfl

theorem cell22_120054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_120054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120054 prefixEnd_120054 := by exact prefixLift 120054
  have htrace : WordTrace (prefixWord ++ tailWord_120054) baseStart_120054 baseEnd_120054 := by
    simpa [prefixWord, tailWord_120054, baseEnd_120054] using wordTrace_append hprefix tailTrace_120054
  have hstable : (prefixWord ++ tailWord_120054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120054).length < 2 ^ (prefixWord ++ tailWord_120054).sum := by decide
  have hdescent : baseEnd_120054 < baseStart_120054 := by decide
  rcases family_descends (prefixWord ++ tailWord_120054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120069 : List Nat := [1, 3, 1, 1, 2, 1, 5, 2, 1, 5]
def baseStart_120069 : Nat := 118140960795 + 120069 * 2 ^ 59
def prefixEnd_120069 : Nat := 4983230072969 + 3 ^ 40 * 120069 * 2
def baseEnd_120069 : Nat := 41102072469863975456879

theorem tailTrace_120069 : CollatzResearch.WordTrace tailWord_120069 prefixEnd_120069 41102072469863975456879 := by
  unfold tailWord_120069
  simp only [CollatzResearch.WordTrace]
  refine ⟨4379276202017993997731261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2919517468011995998487507 4379276202017993997731261)
  ·
    refine ⟨1642228575756747749149223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4379276202017993997731261 1642228575756747749149223)
    ·
      refine ⟨2463342863635121623723835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1642228575756747749149223 2463342863635121623723835)
      ·
        refine ⟨3695014295452682435585753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2463342863635121623723835 3695014295452682435585753)
        ·
          refine ⟨2771260721589511826689315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3695014295452682435585753 2771260721589511826689315)
          ·
            refine ⟨4156891082384267740033973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2771260721589511826689315 4156891082384267740033973)
            ·
              refine ⟨389708538973525100628185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4156891082384267740033973 389708538973525100628185)
              ·
                refine ⟨292281404230143825471139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389708538973525100628185 292281404230143825471139)
                ·
                  refine ⟨438422106345215738206709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292281404230143825471139 438422106345215738206709)
                  ·
                    refine ⟨41102072469863975456879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 438422106345215738206709 41102072469863975456879)
                    ·
                      rfl

theorem cell22_120069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_120069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120069 prefixEnd_120069 := by exact prefixLift 120069
  have htrace : WordTrace (prefixWord ++ tailWord_120069) baseStart_120069 baseEnd_120069 := by
    simpa [prefixWord, tailWord_120069, baseEnd_120069] using wordTrace_append hprefix tailTrace_120069
  have hstable : (prefixWord ++ tailWord_120069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120069).length < 2 ^ (prefixWord ++ tailWord_120069).sum := by decide
  have hdescent : baseEnd_120069 < baseStart_120069 := by decide
  rcases family_descends (prefixWord ++ tailWord_120069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120088 : List Nat := [2, 1, 2, 3, 1, 3, 4, 2, 4]
def baseStart_120088 : Nat := 118140960795 + 120088 * 2 ^ 59
def prefixEnd_120088 : Nat := 4983230072969 + 3 ^ 40 * 120088 * 2
def baseEnd_120088 : Nat := 13702858852718086410607

theorem tailTrace_120088 : CollatzResearch.WordTrace tailWord_120088 prefixEnd_120088 13702858852718086410607 := by
  unfold tailWord_120088
  simp only [CollatzResearch.WordTrace]
  refine ⟨2189984594474580121336459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2919979459299440161781945 2189984594474580121336459)
  ·
    refine ⟨3284976891711870182004689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2189984594474580121336459 3284976891711870182004689)
    ·
      refine ⟨2463732668783902636503517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3284976891711870182004689 2463732668783902636503517)
      ·
        refine ⟨923899750793963488688819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2463732668783902636503517 923899750793963488688819)
        ·
          refine ⟨1385849626190945233033229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923899750793963488688819 1385849626190945233033229)
          ·
            refine ⟨519693609821604462387461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1385849626190945233033229 519693609821604462387461)
            ·
              refine ⟨97442551841550836697649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 519693609821604462387461 97442551841550836697649)
              ·
                refine ⟨73081913881163127523237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97442551841550836697649 73081913881163127523237)
                ·
                  refine ⟨13702858852718086410607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73081913881163127523237 13702858852718086410607)
                  ·
                    rfl

theorem cell22_120088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 4].length) (baseStart_120088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120088 prefixEnd_120088 := by exact prefixLift 120088
  have htrace : WordTrace (prefixWord ++ tailWord_120088) baseStart_120088 baseEnd_120088 := by
    simpa [prefixWord, tailWord_120088, baseEnd_120088] using wordTrace_append hprefix tailTrace_120088
  have hstable : (prefixWord ++ tailWord_120088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120088).length < 2 ^ (prefixWord ++ tailWord_120088).sum := by decide
  have hdescent : baseEnd_120088 < baseStart_120088 := by decide
  rcases family_descends (prefixWord ++ tailWord_120088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120099 : List Nat := [1, 1, 1, 4, 2, 3, 3, 7]
def baseStart_120099 : Nat := 118140960795 + 120099 * 2 ^ 59
def prefixEnd_120099 : Nat := 4983230072969 + 3 ^ 40 * 120099 * 2
def baseEnd_120099 : Nat := 4568038009217099689643

theorem tailTrace_120099 : CollatzResearch.WordTrace tailWord_120099 prefixEnd_120099 4568038009217099689643 := by
  unfold tailWord_120099
  simp only [CollatzResearch.WordTrace]
  refine ⟨4380370391909309121323351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2920246927939539414215567 4380370391909309121323351)
  ·
    refine ⟨6570555587863963681985027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4380370391909309121323351 6570555587863963681985027)
    ·
      refine ⟨9855833381795945522977541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6570555587863963681985027 9855833381795945522977541)
      ·
        refine ⟨1847968759086739785558289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9855833381795945522977541 1847968759086739785558289)
        ·
          refine ⟨1385976569315054839168717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1847968759086739785558289 1385976569315054839168717)
          ·
            refine ⟨519741213493145564688269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1385976569315054839168717 519741213493145564688269)
            ·
              refine ⟨194902955059929586758101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 519741213493145564688269 194902955059929586758101)
              ·
                refine ⟨4568038009217099689643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 194902955059929586758101 4568038009217099689643)
                ·
                  rfl

theorem cell22_120099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 7].length) (baseStart_120099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120099 prefixEnd_120099 := by exact prefixLift 120099
  have htrace : WordTrace (prefixWord ++ tailWord_120099) baseStart_120099 baseEnd_120099 := by
    simpa [prefixWord, tailWord_120099, baseEnd_120099] using wordTrace_append hprefix tailTrace_120099
  have hstable : (prefixWord ++ tailWord_120099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120099).length < 2 ^ (prefixWord ++ tailWord_120099).sum := by decide
  have hdescent : baseEnd_120099 < baseStart_120099 := by decide
  rcases family_descends (prefixWord ++ tailWord_120099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120144 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 7]
def baseStart_120144 : Nat := 118140960795 + 120144 * 2 ^ 59
def prefixEnd_120144 : Nat := 4983230072969 + 3 ^ 40 * 120144 * 2
def baseEnd_120144 : Nat := 13709248834196259943883

theorem tailTrace_120144 : CollatzResearch.WordTrace tailWord_120144 prefixEnd_120144 13709248834196259943883 := by
  unfold tailWord_120144
  simp only [CollatzResearch.WordTrace]
  refine ⟨2191005838373140903355743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2921341117830854537807657 2191005838373140903355743)
  ·
    refine ⟨3286508757559711355033615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2191005838373140903355743 3286508757559711355033615)
    ·
      refine ⟨4929763136339567032550423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3286508757559711355033615 4929763136339567032550423)
      ·
        refine ⟨7394644704509350548825635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4929763136339567032550423 7394644704509350548825635)
        ·
          refine ⟨11091967056764025823238453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7394644704509350548825635 11091967056764025823238453)
          ·
            refine ⟨1039871911571627420928605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11091967056764025823238453 1039871911571627420928605)
            ·
              refine ⟨389951966839360282848227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1039871911571627420928605 389951966839360282848227)
              ·
                refine ⟨584927950259040424272341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389951966839360282848227 584927950259040424272341)
                ·
                  refine ⟨13709248834196259943883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 584927950259040424272341 13709248834196259943883)
                  ·
                    rfl

theorem cell22_120144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 7].length) (baseStart_120144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120144 prefixEnd_120144 := by exact prefixLift 120144
  have htrace : WordTrace (prefixWord ++ tailWord_120144) baseStart_120144 baseEnd_120144 := by
    simpa [prefixWord, tailWord_120144, baseEnd_120144] using wordTrace_append hprefix tailTrace_120144
  have hstable : (prefixWord ++ tailWord_120144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120144).length < 2 ^ (prefixWord ++ tailWord_120144).sum := by decide
  have hdescent : baseEnd_120144 < baseStart_120144 := by decide
  rcases family_descends (prefixWord ++ tailWord_120144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120148 : List Nat := [2, 4, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_120148 : Nat := 118140960795 + 120148 * 2 ^ 59
def prefixEnd_120148 : Nat := 4983230072969 + 3 ^ 40 * 120148 * 2
def baseEnd_120148 : Nat := 41129115784334102731637

theorem tailTrace_120148 : CollatzResearch.WordTrace tailWord_120148 prefixEnd_120148 41129115784334102731637 := by
  unfold tailWord_120148
  simp only [CollatzResearch.WordTrace]
  refine ⟨2191078784365895244928549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2921438379154526993238065 2191078784365895244928549)
  ·
    refine ⟨410827272068605358424103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2191078784365895244928549 410827272068605358424103)
    ·
      refine ⟨616240908102908037636155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410827272068605358424103 616240908102908037636155)
      ·
        refine ⟨924361362154362056454233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616240908102908037636155 924361362154362056454233)
        ·
          refine ⟨693271021615771542340675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 924361362154362056454233 693271021615771542340675)
          ·
            refine ⟨1039906532423657313511013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693271021615771542340675 1039906532423657313511013)
            ·
              refine ⟨194982474829435746283315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1039906532423657313511013 194982474829435746283315)
              ·
                refine ⟨292473712244153619424973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194982474829435746283315 292473712244153619424973)
                ·
                  refine ⟨109677642091557607284365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292473712244153619424973 109677642091557607284365)
                  ·
                    refine ⟨41129115784334102731637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109677642091557607284365 41129115784334102731637)
                    ·
                      rfl

theorem cell22_120148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_120148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120148 prefixEnd_120148 := by exact prefixLift 120148
  have htrace : WordTrace (prefixWord ++ tailWord_120148) baseStart_120148 baseEnd_120148 := by
    simpa [prefixWord, tailWord_120148, baseEnd_120148] using wordTrace_append hprefix tailTrace_120148
  have hstable : (prefixWord ++ tailWord_120148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120148).length < 2 ^ (prefixWord ++ tailWord_120148).sum := by decide
  have hdescent : baseEnd_120148 < baseStart_120148 := by decide
  rcases family_descends (prefixWord ++ tailWord_120148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120236 : List Nat := [2, 2, 1, 1, 1, 1, 5, 3, 2, 4]
def baseStart_120236 : Nat := 118140960795 + 120236 * 2 ^ 59
def prefixEnd_120236 : Nat := 4983230072969 + 3 ^ 40 * 120236 * 2
def baseEnd_120236 : Nat := 41159239982731206531367

theorem tailTrace_120236 : CollatzResearch.WordTrace tailWord_120236 prefixEnd_120236 41159239982731206531367 := by
  unfold tailWord_120236
  simp only [CollatzResearch.WordTrace]
  refine ⟨2192683596206490759530281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2923578128275321012707041 2192683596206490759530281)
  ·
    refine ⟨1644512697154868069647711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2192683596206490759530281 1644512697154868069647711)
    ·
      refine ⟨2466769045732302104471567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1644512697154868069647711 2466769045732302104471567)
      ·
        refine ⟨3700153568598453156707351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2466769045732302104471567 3700153568598453156707351)
        ·
          refine ⟨5550230352897679735061027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3700153568598453156707351 5550230352897679735061027)
          ·
            refine ⟨8325345529346519602591541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5550230352897679735061027 8325345529346519602591541)
            ·
              refine ⟨780501143376236212742957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8325345529346519602591541 780501143376236212742957)
              ·
                refine ⟨292687928766088579778609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 780501143376236212742957 292687928766088579778609)
                ·
                  refine ⟨219515946574566434833957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292687928766088579778609 219515946574566434833957)
                  ·
                    refine ⟨41159239982731206531367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 219515946574566434833957 41159239982731206531367)
                    ·
                      rfl

theorem cell22_120236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_120236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120236 prefixEnd_120236 := by exact prefixLift 120236
  have htrace : WordTrace (prefixWord ++ tailWord_120236) baseStart_120236 baseEnd_120236 := by
    simpa [prefixWord, tailWord_120236, baseEnd_120236] using wordTrace_append hprefix tailTrace_120236
  have hstable : (prefixWord ++ tailWord_120236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120236).length < 2 ^ (prefixWord ++ tailWord_120236).sum := by decide
  have hdescent : baseEnd_120236 < baseStart_120236 := by decide
  rcases family_descends (prefixWord ++ tailWord_120236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120268 : List Nat := [2, 2, 1, 4, 2, 3, 1, 7]
def baseStart_120268 : Nat := 118140960795 + 120268 * 2 ^ 59
def prefixEnd_120268 : Nat := 4983230072969 + 3 ^ 40 * 120268 * 2
def baseEnd_120268 : Nat := 4574466026299309970141

theorem tailTrace_120268 : CollatzResearch.WordTrace tailWord_120268 prefixEnd_120268 4574466026299309970141 := by
  unfold tailWord_120268
  simp only [CollatzResearch.WordTrace]
  refine ⟨2193267164148525492112729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2924356218864700656150305 2193267164148525492112729)
  ·
    refine ⟨1644950373111394119084547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2193267164148525492112729 1644950373111394119084547)
    ·
      refine ⟨2467425559667091178626821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1644950373111394119084547 2467425559667091178626821)
      ·
        refine ⟨462642292437579595992529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2467425559667091178626821 462642292437579595992529)
        ·
          refine ⟨346981719328184696994397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462642292437579595992529 346981719328184696994397)
          ·
            refine ⟨130118144748069261372899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346981719328184696994397 130118144748069261372899)
            ·
              refine ⟨195177217122103892059349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130118144748069261372899 195177217122103892059349)
              ·
                refine ⟨4574466026299309970141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 195177217122103892059349 4574466026299309970141)
                ·
                  rfl

theorem cell22_120268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 7].length) (baseStart_120268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120268 prefixEnd_120268 := by exact prefixLift 120268
  have htrace : WordTrace (prefixWord ++ tailWord_120268) baseStart_120268 baseEnd_120268 := by
    simpa [prefixWord, tailWord_120268, baseEnd_120268] using wordTrace_append hprefix tailTrace_120268
  have hstable : (prefixWord ++ tailWord_120268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120268).length < 2 ^ (prefixWord ++ tailWord_120268).sum := by decide
  have hdescent : baseEnd_120268 < baseStart_120268 := by decide
  rcases family_descends (prefixWord ++ tailWord_120268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120296 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 7]
def baseStart_120296 : Nat := 118140960795 + 120296 * 2 ^ 59
def prefixEnd_120296 : Nat := 4983230072969 + 3 ^ 40 * 120296 * 2
def baseEnd_120296 : Nat := 13726593069637016677061

theorem tailTrace_120296 : CollatzResearch.WordTrace tailWord_120296 prefixEnd_120296 13726593069637016677061 := by
  unfold tailWord_120296
  simp only [CollatzResearch.WordTrace]
  refine ⟨2193777786097805883122371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2925037048130407844163161 2193777786097805883122371)
  ·
    refine ⟨3290666679146708824683557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2193777786097805883122371 3290666679146708824683557)
    ·
      refine ⟨617000002340007904628167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3290666679146708824683557 617000002340007904628167)
      ·
        refine ⟨925500003510011856942251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617000002340007904628167 925500003510011856942251)
        ·
          refine ⟨1388250005265017785413377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925500003510011856942251 1388250005265017785413377)
          ·
            refine ⟨1041187503948763339060033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1388250005265017785413377 1041187503948763339060033)
            ·
              refine ⟨780890627961572504295025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1041187503948763339060033 780890627961572504295025)
              ·
                refine ⟨585667970971179378221269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780890627961572504295025 585667970971179378221269)
                ·
                  refine ⟨13726593069637016677061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 585667970971179378221269 13726593069637016677061)
                  ·
                    rfl

theorem cell22_120296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 7].length) (baseStart_120296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120296 prefixEnd_120296 := by exact prefixLift 120296
  have htrace : WordTrace (prefixWord ++ tailWord_120296) baseStart_120296 baseEnd_120296 := by
    simpa [prefixWord, tailWord_120296, baseEnd_120296] using wordTrace_append hprefix tailTrace_120296
  have hstable : (prefixWord ++ tailWord_120296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120296).length < 2 ^ (prefixWord ++ tailWord_120296).sum := by decide
  have hdescent : baseEnd_120296 < baseStart_120296 := by decide
  rcases family_descends (prefixWord ++ tailWord_120296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120330 : List Nat := [3, 1, 2, 2, 2, 3, 3, 1, 5]
def baseStart_120330 : Nat := 118140960795 + 120330 * 2 ^ 59
def prefixEnd_120330 : Nat := 4983230072969 + 3 ^ 40 * 120330 * 2
def baseEnd_120330 : Nat := 13730472701248764893693

theorem tailTrace_120330 : CollatzResearch.WordTrace tailWord_120330 prefixEnd_120330 13730472701248764893693 := by
  unfold tailWord_120330
  simp only [CollatzResearch.WordTrace]
  refine ⟨1097198913518108893245611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2925863769381623715321629 1097198913518108893245611)
  ·
    refine ⟨1645798370277163339868417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1097198913518108893245611 1645798370277163339868417)
    ·
      refine ⟨1234348777707872504901313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1645798370277163339868417 1234348777707872504901313)
      ·
        refine ⟨925761583280904378675985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1234348777707872504901313 925761583280904378675985)
        ·
          refine ⟨694321187460678284006989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 925761583280904378675985 694321187460678284006989)
          ·
            refine ⟨260370445297754356502621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 694321187460678284006989 260370445297754356502621)
            ·
              refine ⟨97638916986657883688483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260370445297754356502621 97638916986657883688483)
              ·
                refine ⟨146458375479986825532725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97638916986657883688483 146458375479986825532725)
                ·
                  refine ⟨13730472701248764893693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146458375479986825532725 13730472701248764893693)
                  ·
                    rfl

theorem cell22_120330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_120330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120330 prefixEnd_120330 := by exact prefixLift 120330
  have htrace : WordTrace (prefixWord ++ tailWord_120330) baseStart_120330 baseEnd_120330 := by
    simpa [prefixWord, tailWord_120330, baseEnd_120330] using wordTrace_append hprefix tailTrace_120330
  have hstable : (prefixWord ++ tailWord_120330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120330).length < 2 ^ (prefixWord ++ tailWord_120330).sum := by decide
  have hdescent : baseEnd_120330 < baseStart_120330 := by decide
  rcases family_descends (prefixWord ++ tailWord_120330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120448 : List Nat := [2, 1, 1, 2, 1, 4, 1, 5, 5]
def baseStart_120448 : Nat := 118140960795 + 120448 * 2 ^ 59
def prefixEnd_120448 : Nat := 4983230072969 + 3 ^ 40 * 120448 * 2
def baseEnd_120448 : Nat := 13743937305077773410239

theorem tailTrace_120448 : CollatzResearch.WordTrace tailWord_120448 prefixEnd_120448 13743937305077773410239 := by
  unfold tailWord_120448
  simp only [CollatzResearch.WordTrace]
  refine ⟨2196549733822470862888999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2928732978429961150518665 2196549733822470862888999)
  ·
    refine ⟨3294824600733706294333499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2196549733822470862888999 3294824600733706294333499)
    ·
      refine ⟨4942236901100559441500249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3294824600733706294333499 4942236901100559441500249)
      ·
        refine ⟨3706677675825419581125187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4942236901100559441500249 3706677675825419581125187)
        ·
          refine ⟨5560016513738129371687781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706677675825419581125187 5560016513738129371687781)
          ·
            refine ⟨1042503096325899257191459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5560016513738129371687781 1042503096325899257191459)
            ·
              refine ⟨1563754644488848885787189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042503096325899257191459 1563754644488848885787189)
              ·
                refine ⟨146601997920829583042549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1563754644488848885787189 146601997920829583042549)
                ·
                  refine ⟨13743937305077773410239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146601997920829583042549 13743937305077773410239)
                  ·
                    rfl

theorem cell22_120448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 5].length) (baseStart_120448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120448 prefixEnd_120448 := by exact prefixLift 120448
  have htrace : WordTrace (prefixWord ++ tailWord_120448) baseStart_120448 baseEnd_120448 := by
    simpa [prefixWord, tailWord_120448, baseEnd_120448] using wordTrace_append hprefix tailTrace_120448
  have hstable : (prefixWord ++ tailWord_120448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120448).length < 2 ^ (prefixWord ++ tailWord_120448).sum := by decide
  have hdescent : baseEnd_120448 < baseStart_120448 := by decide
  rcases family_descends (prefixWord ++ tailWord_120448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120452 : List Nat := [2, 3, 2, 1, 4, 1, 1, 2, 3, 3]
def baseStart_120452 : Nat := 118140960795 + 120452 * 2 ^ 59
def prefixEnd_120452 : Nat := 4983230072969 + 3 ^ 40 * 120452 * 2
def baseEnd_120452 : Nat := 41233181196978643130705

theorem tailTrace_120452 : CollatzResearch.WordTrace tailWord_120452 prefixEnd_120452 41233181196978643130705 := by
  unfold tailWord_120452
  simp only [CollatzResearch.WordTrace]
  refine ⟨2196622679815225204461805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2928830239753633605949073 2196622679815225204461805)
  ·
    refine ⟨823733504930709451673177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2196622679815225204461805 823733504930709451673177)
    ·
      refine ⟨617800128698032088754883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 823733504930709451673177 617800128698032088754883)
      ·
        refine ⟨926700193047048133132325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617800128698032088754883 926700193047048133132325)
        ·
          refine ⟨173756286196321524962311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 926700193047048133132325 173756286196321524962311)
          ·
            refine ⟨260634429294482287443467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173756286196321524962311 260634429294482287443467)
            ·
              refine ⟨390951643941723431165201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260634429294482287443467 390951643941723431165201)
              ·
                refine ⟨293213732956292573373901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390951643941723431165201 293213732956292573373901)
                ·
                  refine ⟨109955149858609715015213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293213732956292573373901 109955149858609715015213)
                  ·
                    refine ⟨41233181196978643130705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109955149858609715015213 41233181196978643130705)
                    ·
                      rfl

theorem cell22_120452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_120452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120452 prefixEnd_120452 := by exact prefixLift 120452
  have htrace : WordTrace (prefixWord ++ tailWord_120452) baseStart_120452 baseEnd_120452 := by
    simpa [prefixWord, tailWord_120452, baseEnd_120452] using wordTrace_append hprefix tailTrace_120452
  have hstable : (prefixWord ++ tailWord_120452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120452).length < 2 ^ (prefixWord ++ tailWord_120452).sum := by decide
  have hdescent : baseEnd_120452 < baseStart_120452 := by decide
  rcases family_descends (prefixWord ++ tailWord_120452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120482 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 7]
def baseStart_120482 : Nat := 118140960795 + 120482 * 2 ^ 59
def prefixEnd_120482 : Nat := 4983230072969 + 3 ^ 40 * 120482 * 2
def baseEnd_120482 : Nat := 13747816936689521626871

theorem tailTrace_120482 : CollatzResearch.WordTrace tailWord_120482 prefixEnd_120482 13747816936689521626871 := by
  unfold tailWord_120482
  simp only [CollatzResearch.WordTrace]
  refine ⟨1098584887380441383128925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2929559699681177021677133 1098584887380441383128925)
  ·
    refine ⟨411969332767665518673347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1098584887380441383128925 411969332767665518673347)
    ·
      refine ⟨617953999151498278010021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411969332767665518673347 617953999151498278010021)
      ·
        refine ⟨115866374840905927126879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 617953999151498278010021 115866374840905927126879)
        ·
          refine ⟨173799562261358890690319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115866374840905927126879 173799562261358890690319)
          ·
            refine ⟨260699343392038336035479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173799562261358890690319 260699343392038336035479)
            ·
              refine ⟨391049015088057504053219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260699343392038336035479 391049015088057504053219)
              ·
                refine ⟨586573522632086256079829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391049015088057504053219 586573522632086256079829)
                ·
                  refine ⟨13747816936689521626871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 586573522632086256079829 13747816936689521626871)
                  ·
                    rfl

theorem cell22_120482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_120482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120482 prefixEnd_120482 := by exact prefixLift 120482
  have htrace : WordTrace (prefixWord ++ tailWord_120482) baseStart_120482 baseEnd_120482 := by
    simpa [prefixWord, tailWord_120482, baseEnd_120482] using wordTrace_append hprefix tailTrace_120482
  have hstable : (prefixWord ++ tailWord_120482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120482).length < 2 ^ (prefixWord ++ tailWord_120482).sum := by decide
  have hdescent : baseEnd_120482 < baseStart_120482 := by decide
  rcases family_descends (prefixWord ++ tailWord_120482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120510 : List Nat := [4, 2, 1, 1, 2, 2, 2, 2, 6]
def baseStart_120510 : Nat := 118140960795 + 120510 * 2 ^ 59
def prefixEnd_120510 : Nat := 4983230072969 + 3 ^ 40 * 120510 * 2
def baseEnd_120510 : Nat := 13751011927428608393509

theorem tailTrace_120510 : CollatzResearch.WordTrace tailWord_120510 prefixEnd_120510 13751011927428608393509 := by
  unfold tailWord_120510
  simp only [CollatzResearch.WordTrace]
  refine ⟨549420099177540789316873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2930240528946884209689989 549420099177540789316873)
  ·
    refine ⟨412065074383155591987655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 549420099177540789316873 412065074383155591987655)
    ·
      refine ⟨618097611574733387981483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412065074383155591987655 618097611574733387981483)
      ·
        refine ⟨927146417362100081972225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618097611574733387981483 927146417362100081972225)
        ·
          refine ⟨695359813021575061479169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 927146417362100081972225 695359813021575061479169)
          ·
            refine ⟨521519859766181296109377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 695359813021575061479169 521519859766181296109377)
            ·
              refine ⟨391139894824635972082033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 521519859766181296109377 391139894824635972082033)
              ·
                refine ⟨293354921118476979061525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391139894824635972082033 293354921118476979061525)
                ·
                  refine ⟨13751011927428608393509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 293354921118476979061525 13751011927428608393509)
                  ·
                    rfl

theorem cell22_120510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_120510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120510 prefixEnd_120510 := by exact prefixLift 120510
  have htrace : WordTrace (prefixWord ++ tailWord_120510) baseStart_120510 baseEnd_120510 := by
    simpa [prefixWord, tailWord_120510, baseEnd_120510] using wordTrace_append hprefix tailTrace_120510
  have hstable : (prefixWord ++ tailWord_120510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120510).length < 2 ^ (prefixWord ++ tailWord_120510).sum := by decide
  have hdescent : baseEnd_120510 < baseStart_120510 := by decide
  rcases family_descends (prefixWord ++ tailWord_120510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120523 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 6, 4]
def baseStart_120523 : Nat := 118140960795 + 120523 * 2 ^ 59
def prefixEnd_120523 : Nat := 4983230072969 + 3 ^ 40 * 120523 * 2
def baseEnd_120523 : Nat := 41257485947958124605487

theorem tailTrace_120523 : CollatzResearch.WordTrace tailWord_120523 prefixEnd_120523 41257485947958124605487 := by
  unfold tailWord_120523
  simp only [CollatzResearch.WordTrace]
  refine ⟨4395834942373229534758223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2930556628248819689838815 4395834942373229534758223)
  ·
    refine ⟨6593752413559844302137335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4395834942373229534758223 6593752413559844302137335)
    ·
      refine ⟨9890628620339766453206003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6593752413559844302137335 9890628620339766453206003)
      ·
        refine ⟨14835942930509649679809005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9890628620339766453206003 14835942930509649679809005)
        ·
          refine ⟨5563478598941118629928377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14835942930509649679809005 5563478598941118629928377)
          ·
            refine ⟨4172608949205838972446283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5563478598941118629928377 4172608949205838972446283)
            ·
              refine ⟨6258913423808758458669425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4172608949205838972446283 6258913423808758458669425)
              ·
                refine ⟨4694185067856568844002069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6258913423808758458669425 4694185067856568844002069)
                ·
                  refine ⟨220039925055776664562597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4694185067856568844002069 220039925055776664562597)
                  ·
                    refine ⟨41257485947958124605487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 220039925055776664562597 41257485947958124605487)
                    ·
                      rfl

theorem cell22_120523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 4].length) (baseStart_120523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120523 prefixEnd_120523 := by exact prefixLift 120523
  have htrace : WordTrace (prefixWord ++ tailWord_120523) baseStart_120523 baseEnd_120523 := by
    simpa [prefixWord, tailWord_120523, baseEnd_120523] using wordTrace_append hprefix tailTrace_120523
  have hstable : (prefixWord ++ tailWord_120523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120523).length < 2 ^ (prefixWord ++ tailWord_120523).sum := by decide
  have hdescent : baseEnd_120523 < baseStart_120523 := by decide
  rcases family_descends (prefixWord ++ tailWord_120523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120538 : List Nat := [3, 1, 1, 2, 2, 3, 10]
def baseStart_120538 : Nat := 118140960795 + 120538 * 2 ^ 59
def prefixEnd_120538 : Nat := 4983230072969 + 3 ^ 40 * 120538 * 2
def baseEnd_120538 : Nat := 1528245213129743906683

theorem tailTrace_120538 : CollatzResearch.WordTrace tailWord_120538 prefixEnd_120538 1528245213129743906683 := by
  unfold tailWord_120538
  simp only [CollatzResearch.WordTrace]
  refine ⟨1099095509329721774138567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2930921358212591397702845 1099095509329721774138567)
  ·
    refine ⟨1648643263994582661207851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1099095509329721774138567 1648643263994582661207851)
    ·
      refine ⟨2472964895991873991811777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1648643263994582661207851 2472964895991873991811777)
      ·
        refine ⟨1854723671993905493858833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2472964895991873991811777 1854723671993905493858833)
        ·
          refine ⟨1391042753995429120394125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1854723671993905493858833 1391042753995429120394125)
          ·
            refine ⟨521641032748285920147797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1391042753995429120394125 521641032748285920147797)
            ·
              refine ⟨1528245213129743906683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 521641032748285920147797 1528245213129743906683)
              ·
                rfl

theorem cell22_120538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 10].length) (baseStart_120538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120538 prefixEnd_120538 := by exact prefixLift 120538
  have htrace : WordTrace (prefixWord ++ tailWord_120538) baseStart_120538 baseEnd_120538 := by
    simpa [prefixWord, tailWord_120538, baseEnd_120538] using wordTrace_append hprefix tailTrace_120538
  have hstable : (prefixWord ++ tailWord_120538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120538).length < 2 ^ (prefixWord ++ tailWord_120538).sum := by decide
  have hdescent : baseEnd_120538 < baseStart_120538 := by decide
  rcases family_descends (prefixWord ++ tailWord_120538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120568 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 4, 6]
def baseStart_120568 : Nat := 118140960795 + 120568 * 2 ^ 59
def prefixEnd_120568 : Nat := 4983230072969 + 3 ^ 40 * 120568 * 2
def baseEnd_120568 : Nat := 41272890367593007230349

theorem tailTrace_120568 : CollatzResearch.WordTrace tailWord_120568 prefixEnd_120568 41272890367593007230349 := by
  unfold tailWord_120568
  simp only [CollatzResearch.WordTrace]
  refine ⟨2198738113605101110073179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2931650818140134813430905 2198738113605101110073179)
  ·
    refine ⟨3298107170407651665109769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2198738113605101110073179 3298107170407651665109769)
    ·
      refine ⟨2473580377805738748832327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3298107170407651665109769 2473580377805738748832327)
      ·
        refine ⟨3710370566708608123248491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2473580377805738748832327 3710370566708608123248491)
        ·
          refine ⟨5565555850062912184872737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3710370566708608123248491 5565555850062912184872737)
          ·
            refine ⟨4174166887547184138654553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5565555850062912184872737 4174166887547184138654553)
            ·
              refine ⟨3130625165660388103990915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4174166887547184138654553 3130625165660388103990915)
              ·
                refine ⟨4695937748490582155986373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3130625165660388103990915 4695937748490582155986373)
                ·
                  refine ⟨880488327841984154247445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4695937748490582155986373 880488327841984154247445)
                  ·
                    refine ⟨41272890367593007230349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 880488327841984154247445 41272890367593007230349)
                    ·
                      rfl

theorem cell22_120568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_120568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120568 prefixEnd_120568 := by exact prefixLift 120568
  have htrace : WordTrace (prefixWord ++ tailWord_120568) baseStart_120568 baseEnd_120568 := by
    simpa [prefixWord, tailWord_120568, baseEnd_120568] using wordTrace_append hprefix tailTrace_120568
  have hstable : (prefixWord ++ tailWord_120568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120568).length < 2 ^ (prefixWord ++ tailWord_120568).sum := by decide
  have hdescent : baseEnd_120568 < baseStart_120568 := by decide
  rcases family_descends (prefixWord ++ tailWord_120568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120570 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 5, 3]
def baseStart_120570 : Nat := 118140960795 + 120570 * 2 ^ 59
def prefixEnd_120570 : Nat := 4983230072969 + 3 ^ 40 * 120570 * 2
def baseEnd_120570 : Nat := 41273575008465668680343

theorem tailTrace_120570 : CollatzResearch.WordTrace tailWord_120570 prefixEnd_120570 41273575008465668680343 := by
  unfold tailWord_120570
  simp only [CollatzResearch.WordTrace]
  refine ⟨1099387293300739140429791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2931699448801971041146109 1099387293300739140429791)
  ·
    refine ⟨1649080939951108710644687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1099387293300739140429791 1649080939951108710644687)
    ·
      refine ⟨2473621409926663065967031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1649080939951108710644687 2473621409926663065967031)
      ·
        refine ⟨3710432114889994598950547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2473621409926663065967031 3710432114889994598950547)
        ·
          refine ⟨5565648172334991898425821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3710432114889994598950547 5565648172334991898425821)
          ·
            refine ⟨2087118064625621961909683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5565648172334991898425821 2087118064625621961909683)
            ·
              refine ⟨3130677096938432942864525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2087118064625621961909683 3130677096938432942864525)
              ·
                refine ⟨1174003911351912353574197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3130677096938432942864525 1174003911351912353574197)
                ·
                  refine ⟨110062866689241783147581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1174003911351912353574197 110062866689241783147581)
                  ·
                    refine ⟨41273575008465668680343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110062866689241783147581 41273575008465668680343)
                    ·
                      rfl

theorem cell22_120570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_120570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120570 prefixEnd_120570 := by exact prefixLift 120570
  have htrace : WordTrace (prefixWord ++ tailWord_120570) baseStart_120570 baseEnd_120570 := by
    simpa [prefixWord, tailWord_120570, baseEnd_120570] using wordTrace_append hprefix tailTrace_120570
  have hstable : (prefixWord ++ tailWord_120570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120570).length < 2 ^ (prefixWord ++ tailWord_120570).sum := by decide
  have hdescent : baseEnd_120570 < baseStart_120570 := by decide
  rcases family_descends (prefixWord ++ tailWord_120570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120574 : List Nat := [4, 2, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_120574 : Nat := 118140960795 + 120574 * 2 ^ 59
def prefixEnd_120574 : Nat := 4983230072969 + 3 ^ 40 * 120574 * 2
def baseEnd_120574 : Nat := 41274944290210991580331

theorem tailTrace_120574 : CollatzResearch.WordTrace tailWord_120574 prefixEnd_120574 41274944290210991580331 := by
  unfold tailWord_120574
  simp only [CollatzResearch.WordTrace]
  refine ⟨549711883148558155608097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2931796710125643496576517 549711883148558155608097)
  ·
    refine ⟨412283912361418616706073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 549711883148558155608097 412283912361418616706073)
    ·
      refine ⟨309212934271063962529555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412283912361418616706073 309212934271063962529555)
      ·
        refine ⟨463819401406595943794333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309212934271063962529555 463819401406595943794333)
        ·
          refine ⟨173932275527473478922875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 463819401406595943794333 173932275527473478922875)
          ·
            refine ⟨260898413291210218384313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173932275527473478922875 260898413291210218384313)
            ·
              refine ⟨195673809968407663788235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260898413291210218384313 195673809968407663788235)
              ·
                refine ⟨293510714952611495682353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195673809968407663788235 293510714952611495682353)
                ·
                  refine ⟨220133036214458621761765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293510714952611495682353 220133036214458621761765)
                  ·
                    refine ⟨41274944290210991580331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 220133036214458621761765 41274944290210991580331)
                    ·
                      rfl

theorem cell22_120574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_120574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120574 prefixEnd_120574 := by exact prefixLift 120574
  have htrace : WordTrace (prefixWord ++ tailWord_120574) baseStart_120574 baseEnd_120574 := by
    simpa [prefixWord, tailWord_120574, baseEnd_120574] using wordTrace_append hprefix tailTrace_120574
  have hstable : (prefixWord ++ tailWord_120574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120574).length < 2 ^ (prefixWord ++ tailWord_120574).sum := by decide
  have hdescent : baseEnd_120574 < baseStart_120574 := by decide
  rcases family_descends (prefixWord ++ tailWord_120574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120589 : List Nat := [1, 7, 2, 1, 11]
def baseStart_120589 : Nat := 118140960795 + 120589 * 2 ^ 59
def prefixEnd_120589 : Nat := 4983230072969 + 3 ^ 40 * 120589 * 2
def baseEnd_120589 : Nat := 169876868710929845495

theorem tailTrace_120589 : CollatzResearch.WordTrace tailWord_120589 prefixEnd_120589 169876868710929845495 := by
  unfold tailWord_120589
  simp only [CollatzResearch.WordTrace]
  refine ⟨4398242160134122806660821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2932161440089415204440547 4398242160134122806660821)
  ·
    refine ⟨103083800628143503281113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 4398242160134122806660821 103083800628143503281113)
    ·
      refine ⟨77312850471107627460835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103083800628143503281113 77312850471107627460835)
      ·
        refine ⟨115969275706661441191253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77312850471107627460835 115969275706661441191253)
        ·
          refine ⟨169876868710929845495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 115969275706661441191253 169876868710929845495)
          ·
            rfl

theorem cell22_120589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 11].length) (baseStart_120589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120589 prefixEnd_120589 := by exact prefixLift 120589
  have htrace : WordTrace (prefixWord ++ tailWord_120589) baseStart_120589 baseEnd_120589 := by
    simpa [prefixWord, tailWord_120589, baseEnd_120589] using wordTrace_append hprefix tailTrace_120589
  have hstable : (prefixWord ++ tailWord_120589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120589).length < 2 ^ (prefixWord ++ tailWord_120589).sum := by decide
  have hdescent : baseEnd_120589 < baseStart_120589 := by decide
  rcases family_descends (prefixWord ++ tailWord_120589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120600 : List Nat := [2, 1, 2, 3, 1, 1, 3, 4, 5]
def baseStart_120600 : Nat := 118140960795 + 120600 * 2 ^ 59
def prefixEnd_120600 : Nat := 4983230072969 + 3 ^ 40 * 120600 * 2
def baseEnd_120600 : Nat := 13761281540518530143417

theorem tailTrace_120600 : CollatzResearch.WordTrace tailWord_120600 prefixEnd_120600 13761281540518530143417 := by
  unfold tailWord_120600
  simp only [CollatzResearch.WordTrace]
  refine ⟨2199321681547135842655627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2932428908729514456874169 2199321681547135842655627)
  ·
    refine ⟨3298982522320703763983441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2199321681547135842655627 3298982522320703763983441)
    ·
      refine ⟨2474236891740527822987581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3298982522320703763983441 2474236891740527822987581)
      ·
        refine ⟨927838834402697933620343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2474236891740527822987581 927838834402697933620343)
        ·
          refine ⟨1391758251604046900430515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927838834402697933620343 1391758251604046900430515)
          ·
            refine ⟨2087637377406070350645773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391758251604046900430515 2087637377406070350645773)
            ·
              refine ⟨782864016527276381492165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2087637377406070350645773 782864016527276381492165)
              ·
                refine ⟨146787003098864321529781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 782864016527276381492165 146787003098864321529781)
                ·
                  refine ⟨13761281540518530143417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146787003098864321529781 13761281540518530143417)
                  ·
                    rfl

theorem cell22_120600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 5].length) (baseStart_120600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120600 prefixEnd_120600 := by exact prefixLift 120600
  have htrace : WordTrace (prefixWord ++ tailWord_120600) baseStart_120600 baseEnd_120600 := by
    simpa [prefixWord, tailWord_120600, baseEnd_120600] using wordTrace_append hprefix tailTrace_120600
  have hstable : (prefixWord ++ tailWord_120600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120600).length < 2 ^ (prefixWord ++ tailWord_120600).sum := by decide
  have hdescent : baseEnd_120600 < baseStart_120600 := by decide
  rcases family_descends (prefixWord ++ tailWord_120600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120604 : List Nat := [2, 2, 3, 1, 1, 2, 3, 4, 1, 3]
def baseStart_120604 : Nat := 118140960795 + 120604 * 2 ^ 59
def prefixEnd_120604 : Nat := 4983230072969 + 3 ^ 40 * 120604 * 2
def baseEnd_120604 : Nat := 41285213903300913330239

theorem tailTrace_120604 : CollatzResearch.WordTrace tailWord_120604 prefixEnd_120604 41285213903300913330239 := by
  unfold tailWord_120604
  simp only [CollatzResearch.WordTrace]
  refine ⟨2199394627539890184228433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2932526170053186912304577 2199394627539890184228433)
  ·
    refine ⟨1649545970654917638171325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2199394627539890184228433 1649545970654917638171325)
    ·
      refine ⟨618579738995594114314247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1649545970654917638171325 618579738995594114314247)
      ·
        refine ⟨927869608493391171471371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618579738995594114314247 927869608493391171471371)
        ·
          refine ⟨1391804412740086757207057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927869608493391171471371 1391804412740086757207057)
          ·
            refine ⟨1043853309555065067905293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1391804412740086757207057 1043853309555065067905293)
            ·
              refine ⟨391444991083149400464485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1043853309555065067905293 391444991083149400464485)
              ·
                refine ⟨73395935828090512587091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 391444991083149400464485 73395935828090512587091)
                ·
                  refine ⟨110093903742135768880637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73395935828090512587091 110093903742135768880637)
                  ·
                    refine ⟨41285213903300913330239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110093903742135768880637 41285213903300913330239)
                    ·
                      rfl

theorem cell22_120604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_120604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120604 prefixEnd_120604 := by exact prefixLift 120604
  have htrace : WordTrace (prefixWord ++ tailWord_120604) baseStart_120604 baseEnd_120604 := by
    simpa [prefixWord, tailWord_120604, baseEnd_120604] using wordTrace_append hprefix tailTrace_120604
  have hstable : (prefixWord ++ tailWord_120604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120604).length < 2 ^ (prefixWord ++ tailWord_120604).sum := by decide
  have hdescent : baseEnd_120604 < baseStart_120604 := by decide
  rcases family_descends (prefixWord ++ tailWord_120604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120606 : List Nat := [4, 3, 2, 2, 1, 2, 1, 7]
def baseStart_120606 : Nat := 118140960795 + 120606 * 2 ^ 59
def prefixEnd_120606 : Nat := 4983230072969 + 3 ^ 40 * 120606 * 2
def baseEnd_120606 : Nat := 4587322060463730531137

theorem tailTrace_120606 : CollatzResearch.WordTrace tailWord_120606 prefixEnd_120606 4587322060463730531137 := by
  unfold tailWord_120606
  simp only [CollatzResearch.WordTrace]
  refine ⟨549857775134066838753709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2932574800715023140019781 549857775134066838753709)
  ·
    refine ⟨206196665675275064532641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 549857775134066838753709 206196665675275064532641)
    ·
      refine ⟨154647499256456298399481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206196665675275064532641 154647499256456298399481)
      ·
        refine ⟨115985624442342223799611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154647499256456298399481 115985624442342223799611)
        ·
          refine ⟨173978436663513335699417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115985624442342223799611 173978436663513335699417)
          ·
            refine ⟨130483827497635001774563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173978436663513335699417 130483827497635001774563)
            ·
              refine ⟨195725741246452502661845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130483827497635001774563 195725741246452502661845)
              ·
                refine ⟨4587322060463730531137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 195725741246452502661845 4587322060463730531137)
                ·
                  rfl

theorem cell22_120606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_120606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120606 prefixEnd_120606 := by exact prefixLift 120606
  have htrace : WordTrace (prefixWord ++ tailWord_120606) baseStart_120606 baseEnd_120606 := by
    simpa [prefixWord, tailWord_120606, baseEnd_120606] using wordTrace_append hprefix tailTrace_120606
  have hstable : (prefixWord ++ tailWord_120606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120606).length < 2 ^ (prefixWord ++ tailWord_120606).sum := by decide
  have hdescent : baseEnd_120606 < baseStart_120606 := by decide
  rcases family_descends (prefixWord ++ tailWord_120606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120782 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_120782 : Nat := 118140960795 + 120782 * 2 ^ 59
def prefixEnd_120782 : Nat := 4983230072969 + 3 ^ 40 * 120782 * 2
def baseEnd_120782 : Nat := 41346146940967782379693

theorem tailTrace_120782 : CollatzResearch.WordTrace tailWord_120782 prefixEnd_120782 41346146940967782379693 := by
  unfold tailWord_120782
  simp only [CollatzResearch.WordTrace]
  refine ⟨550660181054364596054575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2936854298956611178957733 550660181054364596054575)
  ·
    refine ⟨825990271581546894081863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 550660181054364596054575 825990271581546894081863)
    ·
      refine ⟨1238985407372320341122795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 825990271581546894081863 1238985407372320341122795)
      ·
        refine ⟨1858478111058480511684193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1238985407372320341122795 1858478111058480511684193)
        ·
          refine ⟨1393858583293860383763145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1858478111058480511684193 1393858583293860383763145)
          ·
            refine ⟨1045393937470395287822359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1393858583293860383763145 1045393937470395287822359)
            ·
              refine ⟨1568090906205592931733539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045393937470395287822359 1568090906205592931733539)
              ·
                refine ⟨2352136359308389397600309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1568090906205592931733539 2352136359308389397600309)
                ·
                  refine ⟨220512783685161506025029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2352136359308389397600309 220512783685161506025029)
                  ·
                    refine ⟨41346146940967782379693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 220512783685161506025029 41346146940967782379693)
                    ·
                      rfl

theorem cell22_120782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_120782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120782 prefixEnd_120782 := by exact prefixLift 120782
  have htrace : WordTrace (prefixWord ++ tailWord_120782) baseStart_120782 baseEnd_120782 := by
    simpa [prefixWord, tailWord_120782, baseEnd_120782] using wordTrace_append hprefix tailTrace_120782
  have hstable : (prefixWord ++ tailWord_120782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120782).length < 2 ^ (prefixWord ++ tailWord_120782).sum := by decide
  have hdescent : baseEnd_120782 < baseStart_120782 := by decide
  rcases family_descends (prefixWord ++ tailWord_120782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120827 : List Nat := [1, 1, 1, 1, 1, 3, 4, 4, 2, 4]
def baseStart_120827 : Nat := 118140960795 + 120827 * 2 ^ 59
def prefixEnd_120827 : Nat := 4983230072969 + 3 ^ 40 * 120827 * 2
def baseEnd_120827 : Nat := 41361551360602665004555

theorem tailTrace_120827 : CollatzResearch.WordTrace tailWord_120827 prefixEnd_120827 41361551360602665004555 := by
  unfold tailWord_120827
  simp only [CollatzResearch.WordTrace]
  refine ⟨4406922733271889453824735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2937948488847926302549823 4406922733271889453824735)
  ·
    refine ⟨6610384099907834180737103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4406922733271889453824735 6610384099907834180737103)
    ·
      refine ⟨9915576149861751271105655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6610384099907834180737103 9915576149861751271105655)
      ·
        refine ⟨14873364224792626906658483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9915576149861751271105655 14873364224792626906658483)
        ·
          refine ⟨22310046337188940359987725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14873364224792626906658483 22310046337188940359987725)
          ·
            refine ⟨8366267376445852634995397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22310046337188940359987725 8366267376445852634995397)
            ·
              refine ⟨1568675133083597369061637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8366267376445852634995397 1568675133083597369061637)
              ·
                refine ⟨294126587453174506699057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1568675133083597369061637 294126587453174506699057)
                ·
                  refine ⟨220594940589880880024293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294126587453174506699057 220594940589880880024293)
                  ·
                    refine ⟨41361551360602665004555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 220594940589880880024293 41361551360602665004555)
                    ·
                      rfl

theorem cell22_120827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 4].length) (baseStart_120827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120827 prefixEnd_120827 := by exact prefixLift 120827
  have htrace : WordTrace (prefixWord ++ tailWord_120827) baseStart_120827 baseEnd_120827 := by
    simpa [prefixWord, tailWord_120827, baseEnd_120827] using wordTrace_append hprefix tailTrace_120827
  have hstable : (prefixWord ++ tailWord_120827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120827).length < 2 ^ (prefixWord ++ tailWord_120827).sum := by decide
  have hdescent : baseEnd_120827 < baseStart_120827 := by decide
  rcases family_descends (prefixWord ++ tailWord_120827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120887 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 7]
def baseStart_120887 : Nat := 118140960795 + 120887 * 2 ^ 59
def prefixEnd_120887 : Nat := 4983230072969 + 3 ^ 40 * 120887 * 2
def baseEnd_120887 : Nat := 13794030195594169501457

theorem tailTrace_120887 : CollatzResearch.WordTrace tailWord_120887 prefixEnd_120887 13794030195594169501457 := by
  unfold tailWord_120887
  simp only [CollatzResearch.WordTrace]
  refine ⟨4409111113054519701008915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2939407408703013134005943 4409111113054519701008915)
  ·
    refine ⟨6613666669581779551513373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4409111113054519701008915 6613666669581779551513373)
    ·
      refine ⟨2480125001093167331817515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6613666669581779551513373 2480125001093167331817515)
      ·
        refine ⟨3720187501639750997726273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480125001093167331817515 3720187501639750997726273)
        ·
          refine ⟨2790140626229813248294705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3720187501639750997726273 2790140626229813248294705)
          ·
            refine ⟨2092605469672359936221029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2790140626229813248294705 2092605469672359936221029)
            ·
              refine ⟨392363525563567488041443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2092605469672359936221029 392363525563567488041443)
              ·
                refine ⟨588545288345351232062165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392363525563567488041443 588545288345351232062165)
                ·
                  refine ⟨13794030195594169501457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 588545288345351232062165 13794030195594169501457)
                  ·
                    rfl

theorem cell22_120887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 7].length) (baseStart_120887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120887 prefixEnd_120887 := by exact prefixLift 120887
  have htrace : WordTrace (prefixWord ++ tailWord_120887) baseStart_120887 baseEnd_120887 := by
    simpa [prefixWord, tailWord_120887, baseEnd_120887] using wordTrace_append hprefix tailTrace_120887
  have hstable : (prefixWord ++ tailWord_120887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120887).length < 2 ^ (prefixWord ++ tailWord_120887).sum := by decide
  have hdescent : baseEnd_120887 < baseStart_120887 := by decide
  rcases family_descends (prefixWord ++ tailWord_120887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120983 : List Nat := [1, 1, 3, 3, 4, 1, 2, 3, 4]
def baseStart_120983 : Nat := 118140960795 + 120983 * 2 ^ 59
def prefixEnd_120983 : Nat := 4983230072969 + 3 ^ 40 * 120983 * 2
def baseEnd_120983 : Nat := 13804984449556752701359

theorem tailTrace_120983 : CollatzResearch.WordTrace tailWord_120983 prefixEnd_120983 13804984449556752701359 := by
  unfold tailWord_120983
  simp only [CollatzResearch.WordTrace]
  refine ⟨4412612520706728096503603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2941741680471152064335735 4412612520706728096503603)
  ·
    refine ⟨6618918781060092144755405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4412612520706728096503603 6618918781060092144755405)
    ·
      refine ⟨2482094542897534554283277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6618918781060092144755405 2482094542897534554283277)
      ·
        refine ⟨930785453586575457856229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2482094542897534554283277 930785453586575457856229)
        ·
          refine ⟨174522272547482898348043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 930785453586575457856229 174522272547482898348043)
          ·
            refine ⟨261783408821224347522065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174522272547482898348043 261783408821224347522065)
            ·
              refine ⟨196337556615918260641549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261783408821224347522065 196337556615918260641549)
              ·
                refine ⟨73626583730969347740581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196337556615918260641549 73626583730969347740581)
                ·
                  refine ⟨13804984449556752701359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73626583730969347740581 13804984449556752701359)
                  ·
                    rfl

theorem cell22_120983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 4].length) (baseStart_120983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_120983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_120983 prefixEnd_120983 := by exact prefixLift 120983
  have htrace : WordTrace (prefixWord ++ tailWord_120983) baseStart_120983 baseEnd_120983 := by
    simpa [prefixWord, tailWord_120983, baseEnd_120983] using wordTrace_append hprefix tailTrace_120983
  have hstable : (prefixWord ++ tailWord_120983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120983).length < 2 ^ (prefixWord ++ tailWord_120983).sum := by decide
  have hdescent : baseEnd_120983 < baseStart_120983 := by decide
  rcases family_descends (prefixWord ++ tailWord_120983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121028 : List Nat := [2, 3, 3, 1, 2, 3, 2, 6]
def baseStart_121028 : Nat := 118140960795 + 121028 * 2 ^ 59
def prefixEnd_121028 : Nat := 4983230072969 + 3 ^ 40 * 121028 * 2
def baseEnd_121028 : Nat := 4603373085367237858771

theorem tailTrace_121028 : CollatzResearch.WordTrace tailWord_121028 prefixEnd_121028 4603373085367237858771 := by
  unfold tailWord_121028
  simp only [CollatzResearch.WordTrace]
  refine ⟨2207126902771850390945869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2942835870362467187927825 2207126902771850390945869)
  ·
    refine ⟨827672588539443896604701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2207126902771850390945869 827672588539443896604701)
    ·
      refine ⟨310377220702291461226763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 827672588539443896604701 310377220702291461226763)
      ·
        refine ⟨465565831053437191840145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310377220702291461226763 465565831053437191840145)
        ·
          refine ⟨349174373290077893880109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465565831053437191840145 349174373290077893880109)
          ·
            refine ⟨130940389983779210205041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349174373290077893880109 130940389983779210205041)
            ·
              refine ⟨98205292487834407653781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130940389983779210205041 98205292487834407653781)
              ·
                refine ⟨4603373085367237858771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98205292487834407653781 4603373085367237858771)
                ·
                  rfl

theorem cell22_121028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 6].length) (baseStart_121028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121028 prefixEnd_121028 := by exact prefixLift 121028
  have htrace : WordTrace (prefixWord ++ tailWord_121028) baseStart_121028 baseEnd_121028 := by
    simpa [prefixWord, tailWord_121028, baseEnd_121028] using wordTrace_append hprefix tailTrace_121028
  have hstable : (prefixWord ++ tailWord_121028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121028).length < 2 ^ (prefixWord ++ tailWord_121028).sum := by decide
  have hdescent : baseEnd_121028 < baseStart_121028 := by decide
  rcases family_descends (prefixWord ++ tailWord_121028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121161 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 7, 3]
def baseStart_121161 : Nat := 118140960795 + 121161 * 2 ^ 59
def prefixEnd_121161 : Nat := 4983230072969 + 3 ^ 40 * 121161 * 2
def baseEnd_121161 : Nat := 41475886386337127153531

theorem tailTrace_121161 : CollatzResearch.WordTrace tailWord_121161 prefixEnd_121161 41475886386337127153531 := by
  unfold tailWord_121161
  simp only [CollatzResearch.WordTrace]
  refine ⟨4419104714061864496483337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2946069809374576330988891 4419104714061864496483337)
  ·
    refine ⟨3314328535546398372362503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4419104714061864496483337 3314328535546398372362503)
    ·
      refine ⟨4971492803319597558543755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3314328535546398372362503 4971492803319597558543755)
      ·
        refine ⟨7457239204979396337815633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4971492803319597558543755 7457239204979396337815633)
        ·
          refine ⟨5592929403734547253361725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7457239204979396337815633 5592929403734547253361725)
          ·
            refine ⟨2097348526400455220010647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5592929403734547253361725 2097348526400455220010647)
            ·
              refine ⟨3146022789600682830015971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2097348526400455220010647 3146022789600682830015971)
              ·
                refine ⟨4719034184401024245023957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3146022789600682830015971 4719034184401024245023957)
                ·
                  refine ⟨110602363696899005742749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4719034184401024245023957 110602363696899005742749)
                  ·
                    refine ⟨41475886386337127153531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110602363696899005742749 41475886386337127153531)
                    ·
                      rfl

theorem cell22_121161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 3].length) (baseStart_121161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121161 prefixEnd_121161 := by exact prefixLift 121161
  have htrace : WordTrace (prefixWord ++ tailWord_121161) baseStart_121161 baseEnd_121161 := by
    simpa [prefixWord, tailWord_121161, baseEnd_121161] using wordTrace_append hprefix tailTrace_121161
  have hstable : (prefixWord ++ tailWord_121161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121161).length < 2 ^ (prefixWord ++ tailWord_121161).sum := by decide
  have hdescent : baseEnd_121161 < baseStart_121161 := by decide
  rcases family_descends (prefixWord ++ tailWord_121161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121221 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 5, 4]
def baseStart_121221 : Nat := 118140960795 + 121221 * 2 ^ 59
def prefixEnd_121221 : Nat := 4983230072969 + 3 ^ 40 * 121221 * 2
def baseEnd_121221 : Nat := 41496425612516970653347

theorem tailTrace_121221 : CollatzResearch.WordTrace tailWord_121221 prefixEnd_121221 41496425612516970653347 := by
  unfold tailWord_121221
  simp only [CollatzResearch.WordTrace]
  refine ⟨4421293093844494743667517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2947528729229663162445011 4421293093844494743667517)
  ·
    refine ⟨1657984910191685528875319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4421293093844494743667517 1657984910191685528875319)
    ·
      refine ⟨2486977365287528293312979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1657984910191685528875319 2486977365287528293312979)
      ·
        refine ⟨3730466047931292439969469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2486977365287528293312979 3730466047931292439969469)
        ·
          refine ⟨1398924767974234664988551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3730466047931292439969469 1398924767974234664988551)
          ·
            refine ⟨2098387151961351997482827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398924767974234664988551 2098387151961351997482827)
            ·
              refine ⟨3147580727942027996224241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098387151961351997482827 3147580727942027996224241)
              ·
                refine ⟨2360685545956520997168181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3147580727942027996224241 2360685545956520997168181)
                ·
                  refine ⟨221314269933423843484517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2360685545956520997168181 221314269933423843484517)
                  ·
                    refine ⟨41496425612516970653347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 221314269933423843484517 41496425612516970653347)
                    ·
                      rfl

theorem cell22_121221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_121221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121221 prefixEnd_121221 := by exact prefixLift 121221
  have htrace : WordTrace (prefixWord ++ tailWord_121221) baseStart_121221 baseEnd_121221 := by
    simpa [prefixWord, tailWord_121221, baseEnd_121221] using wordTrace_append hprefix tailTrace_121221
  have hstable : (prefixWord ++ tailWord_121221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121221).length < 2 ^ (prefixWord ++ tailWord_121221).sum := by decide
  have hdescent : baseEnd_121221 < baseStart_121221 := by decide
  rcases family_descends (prefixWord ++ tailWord_121221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121255 : List Nat := [1, 1, 6, 1, 1, 2, 3, 2, 1, 4]
def baseStart_121255 : Nat := 118140960795 + 121255 * 2 ^ 59
def prefixEnd_121255 : Nat := 4983230072969 + 3 ^ 40 * 121255 * 2
def baseEnd_121255 : Nat := 41508064507352215303243

theorem tailTrace_121255 : CollatzResearch.WordTrace tailWord_121255 prefixEnd_121255 41508064507352215303243 := by
  unfold tailWord_121255
  simp only [CollatzResearch.WordTrace]
  refine ⟨4422533175721318550405219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2948355450480879033603479 4422533175721318550405219)
  ·
    refine ⟨6633799763581977825607829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4422533175721318550405219 6633799763581977825607829)
    ·
      refine ⟨310959363917905210575367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6633799763581977825607829 310959363917905210575367)
      ·
        refine ⟨466439045876857815863051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310959363917905210575367 466439045876857815863051)
        ·
          refine ⟨699658568815286723794577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466439045876857815863051 699658568815286723794577)
          ·
            refine ⟨524743926611465042845933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 699658568815286723794577 524743926611465042845933)
            ·
              refine ⟨196778972479299391067225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 524743926611465042845933 196778972479299391067225)
              ·
                refine ⟨147584229359474543300419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196778972479299391067225 147584229359474543300419)
                ·
                  refine ⟨221376344039211814950629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147584229359474543300419 221376344039211814950629)
                  ·
                    refine ⟨41508064507352215303243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 221376344039211814950629 41508064507352215303243)
                    ·
                      rfl

theorem cell22_121255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_121255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121255 prefixEnd_121255 := by exact prefixLift 121255
  have htrace : WordTrace (prefixWord ++ tailWord_121255) baseStart_121255 baseEnd_121255 := by
    simpa [prefixWord, tailWord_121255, baseEnd_121255] using wordTrace_append hprefix tailTrace_121255
  have hstable : (prefixWord ++ tailWord_121255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121255).length < 2 ^ (prefixWord ++ tailWord_121255).sum := by decide
  have hdescent : baseEnd_121255 < baseStart_121255 := by decide
  rcases family_descends (prefixWord ++ tailWord_121255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121287 : List Nat := [1, 1, 4, 1, 1, 6, 2, 2, 4]
def baseStart_121287 : Nat := 118140960795 + 121287 * 2 ^ 59
def prefixEnd_121287 : Nat := 4983230072969 + 3 ^ 40 * 121287 * 2
def baseEnd_121287 : Nat := 13839672920438266167715

theorem tailTrace_121287 : CollatzResearch.WordTrace tailWord_121287 prefixEnd_121287 13839672920438266167715 := by
  unfold tailWord_121287
  simp only [CollatzResearch.WordTrace]
  refine ⟨4423700311605388015570115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2949133541070258677046743 4423700311605388015570115)
  ·
    refine ⟨6635550467408082023355173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4423700311605388015570115 6635550467408082023355173)
    ·
      refine ⟨1244165712639015379379095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6635550467408082023355173 1244165712639015379379095)
      ·
        refine ⟨1866248568958523069068643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244165712639015379379095 1866248568958523069068643)
        ·
          refine ⟨2799372853437784603602965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1866248568958523069068643 2799372853437784603602965)
          ·
            refine ⟨131220602504896153293889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2799372853437784603602965 131220602504896153293889)
            ·
              refine ⟨98415451878672114970417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131220602504896153293889 98415451878672114970417)
              ·
                refine ⟨73811588909004086227813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98415451878672114970417 73811588909004086227813)
                ·
                  refine ⟨13839672920438266167715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73811588909004086227813 13839672920438266167715)
                  ·
                    rfl

theorem cell22_121287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 4].length) (baseStart_121287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121287 prefixEnd_121287 := by exact prefixLift 121287
  have htrace : WordTrace (prefixWord ++ tailWord_121287) baseStart_121287 baseEnd_121287 := by
    simpa [prefixWord, tailWord_121287, baseEnd_121287] using wordTrace_append hprefix tailTrace_121287
  have hstable : (prefixWord ++ tailWord_121287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121287).length < 2 ^ (prefixWord ++ tailWord_121287).sum := by decide
  have hdescent : baseEnd_121287 < baseStart_121287 := by decide
  rcases family_descends (prefixWord ++ tailWord_121287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121302 : List Nat := [5, 2, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_121302 : Nat := 118140960795 + 121302 * 2 ^ 59
def prefixEnd_121302 : Nat := 4983230072969 + 3 ^ 40 * 121302 * 2
def baseEnd_121302 : Nat := 41524153567859759378099

theorem tailTrace_121302 : CollatzResearch.WordTrace tailWord_121302 prefixEnd_121302 41524153567859759378099 := by
  unfold tailWord_121302
  simp only [CollatzResearch.WordTrace]
  refine ⟨276515462909440348585385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2949498271034030384910773 276515462909440348585385)
  ·
    refine ⟨207386597182080261439039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276515462909440348585385 207386597182080261439039)
    ·
      refine ⟨311079895773120392158559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207386597182080261439039 311079895773120392158559)
      ·
        refine ⟨466619843659680588237839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311079895773120392158559 466619843659680588237839)
        ·
          refine ⟨699929765489520882356759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466619843659680588237839 699929765489520882356759)
          ·
            refine ⟨1049894648234281323535139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699929765489520882356759 1049894648234281323535139)
            ·
              refine ⟨1574841972351421985302709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049894648234281323535139 1574841972351421985302709)
              ·
                refine ⟨147641434907945811122129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1574841972351421985302709 147641434907945811122129)
                ·
                  refine ⟨110731076180959358341597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147641434907945811122129 110731076180959358341597)
                  ·
                    refine ⟨41524153567859759378099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110731076180959358341597 41524153567859759378099)
                    ·
                      rfl

theorem cell22_121302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_121302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121302 prefixEnd_121302 := by exact prefixLift 121302
  have htrace : WordTrace (prefixWord ++ tailWord_121302) baseStart_121302 baseEnd_121302 := by
    simpa [prefixWord, tailWord_121302, baseEnd_121302] using wordTrace_append hprefix tailTrace_121302
  have hstable : (prefixWord ++ tailWord_121302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121302).length < 2 ^ (prefixWord ++ tailWord_121302).sum := by decide
  have hdescent : baseEnd_121302 < baseStart_121302 := by decide
  rcases family_descends (prefixWord ++ tailWord_121302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121315 : List Nat := [1, 1, 1, 6, 3, 1, 3, 6]
def baseStart_121315 : Nat := 118140960795 + 121315 * 2 ^ 59
def prefixEnd_121315 : Nat := 4983230072969 + 3 ^ 40 * 121315 * 2
def baseEnd_121315 : Nat := 4614289303725784311451

theorem tailTrace_121315 : CollatzResearch.WordTrace tailWord_121315 prefixEnd_121315 4614289303725784311451 := by
  unfold tailWord_121315
  simp only [CollatzResearch.WordTrace]
  refine ⟨4424721555503948797589399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2949814370335965865059599 4424721555503948797589399)
  ·
    refine ⟨6637082333255923196384099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4424721555503948797589399 6637082333255923196384099)
    ·
      refine ⟨9955623499883884794576149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6637082333255923196384099 9955623499883884794576149)
      ·
        refine ⟨466669851557057099745757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9955623499883884794576149 466669851557057099745757)
        ·
          refine ⟨175001194333896412404659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 466669851557057099745757 175001194333896412404659)
          ·
            refine ⟨262501791500844618606989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175001194333896412404659 262501791500844618606989)
            ·
              refine ⟨98438171812816731977621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262501791500844618606989 98438171812816731977621)
              ·
                refine ⟨4614289303725784311451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98438171812816731977621 4614289303725784311451)
                ·
                  rfl

theorem cell22_121315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 6].length) (baseStart_121315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121315 prefixEnd_121315 := by exact prefixLift 121315
  have htrace : WordTrace (prefixWord ++ tailWord_121315) baseStart_121315 baseEnd_121315 := by
    simpa [prefixWord, tailWord_121315, baseEnd_121315] using wordTrace_append hprefix tailTrace_121315
  have hstable : (prefixWord ++ tailWord_121315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121315).length < 2 ^ (prefixWord ++ tailWord_121315).sum := by decide
  have hdescent : baseEnd_121315 < baseStart_121315 := by decide
  rcases family_descends (prefixWord ++ tailWord_121315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121317 : List Nat := [1, 3, 1, 5, 2, 2, 1, 1, 2, 4]
def baseStart_121317 : Nat := 118140960795 + 121317 * 2 ^ 59
def prefixEnd_121317 : Nat := 4983230072969 + 3 ^ 40 * 121317 * 2
def baseEnd_121317 : Nat := 41529288374404720253053

theorem tailTrace_121317 : CollatzResearch.WordTrace tailWord_121317 prefixEnd_121317 41529288374404720253053 := by
  unfold tailWord_121317
  simp only [CollatzResearch.WordTrace]
  refine ⟨4424794501496703139162205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2949863000997802092774803 4424794501496703139162205)
  ·
    refine ⟨1659297938061263677185827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4424794501496703139162205 1659297938061263677185827)
    ·
      refine ⟨2488946907091895515778741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1659297938061263677185827 2488946907091895515778741)
      ·
        refine ⟨233338772539865204604257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2488946907091895515778741 233338772539865204604257)
        ·
          refine ⟨175004079404898903453193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233338772539865204604257 175004079404898903453193)
          ·
            refine ⟨131253059553674177589895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175004079404898903453193 131253059553674177589895)
            ·
              refine ⟨196879589330511266384843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131253059553674177589895 196879589330511266384843)
              ·
                refine ⟨295319383995766899577265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196879589330511266384843 295319383995766899577265)
                ·
                  refine ⟨221489537996825174682949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295319383995766899577265 221489537996825174682949)
                  ·
                    refine ⟨41529288374404720253053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 221489537996825174682949 41529288374404720253053)
                    ·
                      rfl

theorem cell22_121317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_121317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121317 prefixEnd_121317 := by exact prefixLift 121317
  have htrace : WordTrace (prefixWord ++ tailWord_121317) baseStart_121317 baseEnd_121317 := by
    simpa [prefixWord, tailWord_121317, baseEnd_121317] using wordTrace_append hprefix tailTrace_121317
  have hstable : (prefixWord ++ tailWord_121317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121317).length < 2 ^ (prefixWord ++ tailWord_121317).sum := by decide
  have hdescent : baseEnd_121317 < baseStart_121317 := by decide
  rcases family_descends (prefixWord ++ tailWord_121317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121405 : List Nat := [1, 4, 1, 3, 2, 1, 3, 1, 6]
def baseStart_121405 : Nat := 118140960795 + 121405 * 2 ^ 59
def prefixEnd_121405 : Nat := 4983230072969 + 3 ^ 40 * 121405 * 2
def baseEnd_121405 : Nat := 13853137524267274684261

theorem tailTrace_121405 : CollatzResearch.WordTrace tailWord_121405 prefixEnd_121405 13853137524267274684261 := by
  unfold tailWord_121405
  simp only [CollatzResearch.WordTrace]
  refine ⟨4428004125177894168365669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2952002750118596112243779 4428004125177894168365669)
  ·
    refine ⟨830250773470855156568563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4428004125177894168365669 830250773470855156568563)
    ·
      refine ⟨1245376160206282734852845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 830250773470855156568563 1245376160206282734852845)
      ·
        refine ⟨467016060077356025569817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1245376160206282734852845 467016060077356025569817)
        ·
          refine ⟨350262045058017019177363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467016060077356025569817 350262045058017019177363)
          ·
            refine ⟨525393067587025528766045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350262045058017019177363 525393067587025528766045)
            ·
              refine ⟨197022400345134573287267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 525393067587025528766045 197022400345134573287267)
              ·
                refine ⟨295533600517701859930901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197022400345134573287267 295533600517701859930901)
                ·
                  refine ⟨13853137524267274684261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 295533600517701859930901 13853137524267274684261)
                  ·
                    rfl

theorem cell22_121405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_121405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121405 prefixEnd_121405 := by exact prefixLift 121405
  have htrace : WordTrace (prefixWord ++ tailWord_121405) baseStart_121405 baseEnd_121405 := by
    simpa [prefixWord, tailWord_121405, baseEnd_121405] using wordTrace_append hprefix tailTrace_121405
  have hstable : (prefixWord ++ tailWord_121405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121405).length < 2 ^ (prefixWord ++ tailWord_121405).sum := by decide
  have hdescent : baseEnd_121405 < baseStart_121405 := by decide
  rcases family_descends (prefixWord ++ tailWord_121405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121454 : List Nat := [4, 1, 2, 2, 2, 2, 2, 2, 2, 3]
def baseStart_121454 : Nat := 118140960795 + 121454 * 2 ^ 59
def prefixEnd_121454 : Nat := 4983230072969 + 3 ^ 40 * 121454 * 2
def baseEnd_121454 : Nat := 41576186274182029577633

theorem tailTrace_121454 : CollatzResearch.WordTrace tailWord_121454 prefixEnd_121454 41576186274182029577633 := by
  unfold tailWord_121454
  simp only [CollatzResearch.WordTrace]
  refine ⟨553723912750046942112427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2953194201333583691266277 553723912750046942112427)
  ·
    refine ⟨830585869125070413168641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 553723912750046942112427 830585869125070413168641)
    ·
      refine ⟨622939401843802809876481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 830585869125070413168641 622939401843802809876481)
      ·
        refine ⟨467204551382852107407361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 622939401843802809876481 467204551382852107407361)
        ·
          refine ⟨350403413537139080555521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467204551382852107407361 350403413537139080555521)
          ·
            refine ⟨262802560152854310416641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350403413537139080555521 262802560152854310416641)
            ·
              refine ⟨197101920114640732812481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262802560152854310416641 197101920114640732812481)
              ·
                refine ⟨147826440085980549609361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197101920114640732812481 147826440085980549609361)
                ·
                  refine ⟨110869830064485412207021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147826440085980549609361 110869830064485412207021)
                  ·
                    refine ⟨41576186274182029577633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110869830064485412207021 41576186274182029577633)
                    ·
                      rfl

theorem cell22_121454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_121454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121454 prefixEnd_121454 := by exact prefixLift 121454
  have htrace : WordTrace (prefixWord ++ tailWord_121454) baseStart_121454 baseEnd_121454 := by
    simpa [prefixWord, tailWord_121454, baseEnd_121454] using wordTrace_append hprefix tailTrace_121454
  have hstable : (prefixWord ++ tailWord_121454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121454).length < 2 ^ (prefixWord ++ tailWord_121454).sum := by decide
  have hdescent : baseEnd_121454 < baseStart_121454 := by decide
  rcases family_descends (prefixWord ++ tailWord_121454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121456 : List Nat := [2, 1, 1, 1, 8, 1, 2, 2, 4]
def baseStart_121456 : Nat := 118140960795 + 121456 * 2 ^ 59
def prefixEnd_121456 : Nat := 4983230072969 + 3 ^ 40 * 121456 * 2
def baseEnd_121456 : Nat := 13858956971684897009209

theorem tailTrace_121456 : CollatzResearch.WordTrace tailWord_121456 prefixEnd_121456 13858956971684897009209 := by
  unfold tailWord_121456
  simp only [CollatzResearch.WordTrace]
  refine ⟨2214932123996564939236111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2953242831995419918981481 2214932123996564939236111)
  ·
    refine ⟨3322398185994847408854167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2214932123996564939236111 3322398185994847408854167)
    ·
      refine ⟨4983597278992271113281251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3322398185994847408854167 4983597278992271113281251)
      ·
        refine ⟨7475395918488406669921877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4983597278992271113281251 7475395918488406669921877)
        ·
          refine ⟨87602295919786015663147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 7475395918488406669921877 87602295919786015663147)
          ·
            refine ⟨131403443879679023494721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87602295919786015663147 131403443879679023494721)
            ·
              refine ⟨98552582909759267621041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131403443879679023494721 98552582909759267621041)
              ·
                refine ⟨73914437182319450715781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98552582909759267621041 73914437182319450715781)
                ·
                  refine ⟨13858956971684897009209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73914437182319450715781 13858956971684897009209)
                  ·
                    rfl

theorem cell22_121456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 4].length) (baseStart_121456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121456 prefixEnd_121456 := by exact prefixLift 121456
  have htrace : WordTrace (prefixWord ++ tailWord_121456) baseStart_121456 baseEnd_121456 := by
    simpa [prefixWord, tailWord_121456, baseEnd_121456] using wordTrace_append hprefix tailTrace_121456
  have hstable : (prefixWord ++ tailWord_121456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121456).length < 2 ^ (prefixWord ++ tailWord_121456).sum := by decide
  have hdescent : baseEnd_121456 < baseStart_121456 := by decide
  rcases family_descends (prefixWord ++ tailWord_121456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121463 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 2, 6]
def baseStart_121463 : Nat := 118140960795 + 121463 * 2 ^ 59
def prefixEnd_121463 : Nat := 4983230072969 + 3 ^ 40 * 121463 * 2
def baseEnd_121463 : Nat := 41579267158109006102605

theorem tailTrace_121463 : CollatzResearch.WordTrace tailWord_121463 prefixEnd_121463 41579267158109006102605 := by
  unfold tailWord_121463
  simp only [CollatzResearch.WordTrace]
  refine ⟨4430119558967770073977043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2953413039311846715984695 4430119558967770073977043)
  ·
    refine ⟨6645179338451655110965565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4430119558967770073977043 6645179338451655110965565)
    ·
      refine ⟨2491942251919370666612087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6645179338451655110965565 2491942251919370666612087)
      ·
        refine ⟨3737913377879055999918131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2491942251919370666612087 3737913377879055999918131)
        ·
          refine ⟨5606870066818583999877197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3737913377879055999918131 5606870066818583999877197)
          ·
            refine ⟨2102576275056968999953949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5606870066818583999877197 2102576275056968999953949)
            ·
              refine ⟨788466103146363374982731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2102576275056968999953949 788466103146363374982731)
              ·
                refine ⟨1182699154719545062474097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788466103146363374982731 1182699154719545062474097)
                ·
                  refine ⟨887024366039658796855573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1182699154719545062474097 887024366039658796855573)
                  ·
                    refine ⟨41579267158109006102605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 887024366039658796855573 41579267158109006102605)
                    ·
                      rfl

theorem cell22_121463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_121463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121463 prefixEnd_121463 := by exact prefixLift 121463
  have htrace : WordTrace (prefixWord ++ tailWord_121463) baseStart_121463 baseEnd_121463 := by
    simpa [prefixWord, tailWord_121463, baseEnd_121463] using wordTrace_append hprefix tailTrace_121463
  have hstable : (prefixWord ++ tailWord_121463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121463).length < 2 ^ (prefixWord ++ tailWord_121463).sum := by decide
  have hdescent : baseEnd_121463 < baseStart_121463 := by decide
  rcases family_descends (prefixWord ++ tailWord_121463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121572 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 4, 3]
def baseStart_121572 : Nat := 118140960795 + 121572 * 2 ^ 59
def prefixEnd_121572 : Nat := 4983230072969 + 3 ^ 40 * 121572 * 2
def baseEnd_121572 : Nat := 41616580085669055127271

theorem tailTrace_121572 : CollatzResearch.WordTrace tailWord_121572 prefixEnd_121572 41616580085669055127271 := by
  unfold tailWord_121572
  simp only [CollatzResearch.WordTrace]
  refine ⟨2217047557786440844847485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2956063410381921126463313 2217047557786440844847485)
  ·
    refine ⟨831392834169915316817807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2217047557786440844847485 831392834169915316817807)
    ·
      refine ⟨1247089251254872975226711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 831392834169915316817807 1247089251254872975226711)
      ·
        refine ⟨1870633876882309462840067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1247089251254872975226711 1870633876882309462840067)
        ·
          refine ⟨2805950815323464194260101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1870633876882309462840067 2805950815323464194260101)
          ·
            refine ⟨526115777873149536423769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2805950815323464194260101 526115777873149536423769)
            ·
              refine ⟨394586833404862152317827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526115777873149536423769 394586833404862152317827)
              ·
                refine ⟨591880250107293228476741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394586833404862152317827 591880250107293228476741)
                ·
                  refine ⟨110977546895117480339389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 591880250107293228476741 110977546895117480339389)
                  ·
                    refine ⟨41616580085669055127271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110977546895117480339389 41616580085669055127271)
                    ·
                      rfl

theorem cell22_121572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_121572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121572 prefixEnd_121572 := by exact prefixLift 121572
  have htrace : WordTrace (prefixWord ++ tailWord_121572) baseStart_121572 baseEnd_121572 := by
    simpa [prefixWord, tailWord_121572, baseEnd_121572] using wordTrace_append hprefix tailTrace_121572
  have hstable : (prefixWord ++ tailWord_121572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121572).length < 2 ^ (prefixWord ++ tailWord_121572).sum := by decide
  have hdescent : baseEnd_121572 < baseStart_121572 := by decide
  rcases family_descends (prefixWord ++ tailWord_121572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121585 : List Nat := [1, 2, 2, 2, 2, 2, 4, 7]
def baseStart_121585 : Nat := 118140960795 + 121585 * 2 ^ 59
def prefixEnd_121585 : Nat := 4983230072969 + 3 ^ 40 * 121585 * 2
def baseEnd_121585 : Nat := 4624558916815706061359

theorem tailTrace_121585 : CollatzResearch.WordTrace tailWord_121585 prefixEnd_121585 4624558916815706061359 := by
  unfold tailWord_121585
  simp only [CollatzResearch.WordTrace]
  refine ⟨4434569264525784909918209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2956379509683856606612139 4434569264525784909918209)
  ·
    refine ⟨3325926948394338682438657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4434569264525784909918209 3325926948394338682438657)
    ·
      refine ⟨2494445211295754011828993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3325926948394338682438657 2494445211295754011828993)
      ·
        refine ⟨1870833908471815508871745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2494445211295754011828993 1870833908471815508871745)
        ·
          refine ⟨1403125431353861631653809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1870833908471815508871745 1403125431353861631653809)
          ·
            refine ⟨1052344073515396223740357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1403125431353861631653809 1052344073515396223740357)
            ·
              refine ⟨197314513784136791951317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1052344073515396223740357 197314513784136791951317)
              ·
                refine ⟨4624558916815706061359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 197314513784136791951317 4624558916815706061359)
                ·
                  rfl

theorem cell22_121585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 7].length) (baseStart_121585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121585 prefixEnd_121585 := by exact prefixLift 121585
  have htrace : WordTrace (prefixWord ++ tailWord_121585) baseStart_121585 baseEnd_121585 := by
    simpa [prefixWord, tailWord_121585, baseEnd_121585] using wordTrace_append hprefix tailTrace_121585
  have hstable : (prefixWord ++ tailWord_121585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121585).length < 2 ^ (prefixWord ++ tailWord_121585).sum := by decide
  have hdescent : baseEnd_121585 < baseStart_121585 := by decide
  rcases family_descends (prefixWord ++ tailWord_121585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121602 : List Nat := [3, 4, 1, 1, 1, 2, 2, 8]
def baseStart_121602 : Nat := 118140960795 + 121602 * 2 ^ 59
def prefixEnd_121602 : Nat := 4983230072969 + 3 ^ 40 * 121602 * 2
def baseEnd_121602 : Nat := 4625205522084330764131

theorem tailTrace_121602 : CollatzResearch.WordTrace tailWord_121602 prefixEnd_121602 4625205522084330764131 := by
  unfold tailWord_121602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1108797326366049203321765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2956792870309464542191373 1108797326366049203321765)
  ·
    refine ⟨207899498693634225622831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1108797326366049203321765 207899498693634225622831)
    ·
      refine ⟨311849248040451338434247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207899498693634225622831 311849248040451338434247)
      ·
        refine ⟨467773872060677007651371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311849248040451338434247 467773872060677007651371)
        ·
          refine ⟨701660808091015511477057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467773872060677007651371 701660808091015511477057)
          ·
            refine ⟨526245606068261633607793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701660808091015511477057 526245606068261633607793)
            ·
              refine ⟨394684204551196225205845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526245606068261633607793 394684204551196225205845)
              ·
                refine ⟨4625205522084330764131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 394684204551196225205845 4625205522084330764131)
                ·
                  rfl

theorem cell22_121602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 8].length) (baseStart_121602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121602 prefixEnd_121602 := by exact prefixLift 121602
  have htrace : WordTrace (prefixWord ++ tailWord_121602) baseStart_121602 baseEnd_121602 := by
    simpa [prefixWord, tailWord_121602, baseEnd_121602] using wordTrace_append hprefix tailTrace_121602
  have hstable : (prefixWord ++ tailWord_121602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121602).length < 2 ^ (prefixWord ++ tailWord_121602).sum := by decide
  have hdescent : baseEnd_121602 < baseStart_121602 := by decide
  rcases family_descends (prefixWord ++ tailWord_121602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121681 : List Nat := [1, 2, 2, 1, 7, 1, 1, 2, 5]
def baseStart_121681 : Nat := 118140960795 + 121681 * 2 ^ 59
def prefixEnd_121681 : Nat := 4983230072969 + 3 ^ 40 * 121681 * 2
def baseEnd_121681 : Nat := 13884631004409701383979

theorem tailTrace_121681 : CollatzResearch.WordTrace tailWord_121681 prefixEnd_121681 13884631004409701383979 := by
  unfold tailWord_121681
  simp only [CollatzResearch.WordTrace]
  refine ⟨4438070672177993305412897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2958713781451995536941931 4438070672177993305412897)
  ·
    refine ⟨3328553004133494979059673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4438070672177993305412897 3328553004133494979059673)
    ·
      refine ⟨2496414753100121234294755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3328553004133494979059673 2496414753100121234294755)
      ·
        refine ⟨3744622129650181851442133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2496414753100121234294755 3744622129650181851442133)
        ·
          refine ⟨87764581163676137143175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 3744622129650181851442133 87764581163676137143175)
          ·
            refine ⟨131646871745514205714763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87764581163676137143175 131646871745514205714763)
            ·
              refine ⟨197470307618271308572145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131646871745514205714763 197470307618271308572145)
              ·
                refine ⟨148102730713703481429109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197470307618271308572145 148102730713703481429109)
                ·
                  refine ⟨13884631004409701383979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148102730713703481429109 13884631004409701383979)
                  ·
                    rfl

theorem cell22_121681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 5].length) (baseStart_121681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121681 prefixEnd_121681 := by exact prefixLift 121681
  have htrace : WordTrace (prefixWord ++ tailWord_121681) baseStart_121681 baseEnd_121681 := by
    simpa [prefixWord, tailWord_121681, baseEnd_121681] using wordTrace_append hprefix tailTrace_121681
  have hstable : (prefixWord ++ tailWord_121681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121681).length < 2 ^ (prefixWord ++ tailWord_121681).sum := by decide
  have hdescent : baseEnd_121681 < baseStart_121681 := by decide
  rcases family_descends (prefixWord ++ tailWord_121681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121707 : List Nat := [1, 1, 1, 1, 2, 2, 7, 1, 1, 5]
def baseStart_121707 : Nat := 118140960795 + 121707 * 2 ^ 59
def prefixEnd_121707 : Nat := 4983230072969 + 3 ^ 40 * 121707 * 2
def baseEnd_121707 : Nat := 41662793344573703001857

theorem tailTrace_121707 : CollatzResearch.WordTrace tailWord_121707 prefixEnd_121707 41662793344573703001857 := by
  unfold tailWord_121707
  simp only [CollatzResearch.WordTrace]
  refine ⟨4439018970083799745859375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2959345980055866497239583 4439018970083799745859375)
  ·
    refine ⟨6658528455125699618789063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4439018970083799745859375 6658528455125699618789063)
    ·
      refine ⟨9987792682688549428183595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6658528455125699618789063 9987792682688549428183595)
      ·
        refine ⟨14981689024032824142275393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9987792682688549428183595 14981689024032824142275393)
        ·
          refine ⟨11236266768024618106706545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14981689024032824142275393 11236266768024618106706545)
          ·
            refine ⟨8427200076018463580029909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11236266768024618106706545 8427200076018463580029909)
            ·
              refine ⟨197512501781682740156951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 8427200076018463580029909 197512501781682740156951)
              ·
                refine ⟨296268752672524110235427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197512501781682740156951 296268752672524110235427)
                ·
                  refine ⟨444403129008786165353141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296268752672524110235427 444403129008786165353141)
                  ·
                    refine ⟨41662793344573703001857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 444403129008786165353141 41662793344573703001857)
                    ·
                      rfl

theorem cell22_121707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 5].length) (baseStart_121707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121707 prefixEnd_121707 := by exact prefixLift 121707
  have htrace : WordTrace (prefixWord ++ tailWord_121707) baseStart_121707 baseEnd_121707 := by
    simpa [prefixWord, tailWord_121707, baseEnd_121707] using wordTrace_append hprefix tailTrace_121707
  have hstable : (prefixWord ++ tailWord_121707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121707).length < 2 ^ (prefixWord ++ tailWord_121707).sum := by decide
  have hdescent : baseEnd_121707 < baseStart_121707 := by decide
  rcases family_descends (prefixWord ++ tailWord_121707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121722 : List Nat := [3, 1, 1, 1, 1, 1, 3, 5, 2, 4]
def baseStart_121722 : Nat := 118140960795 + 121722 * 2 ^ 59
def prefixEnd_121722 : Nat := 4983230072969 + 3 ^ 40 * 121722 * 2
def baseEnd_121722 : Nat := 41667928151118663876811

theorem tailTrace_121722 : CollatzResearch.WordTrace tailWord_121722 prefixEnd_121722 41667928151118663876811 := by
  unfold tailWord_121722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1109891516257364326913855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2959710710019638205103613 1109891516257364326913855)
  ·
    refine ⟨1664837274386046490370783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1109891516257364326913855 1664837274386046490370783)
    ·
      refine ⟨2497255911579069735556175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1664837274386046490370783 2497255911579069735556175)
      ·
        refine ⟨3745883867368604603334263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2497255911579069735556175 3745883867368604603334263)
        ·
          refine ⟨5618825801052906905001395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3745883867368604603334263 5618825801052906905001395)
          ·
            refine ⟨8428238701579360357502093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5618825801052906905001395 8428238701579360357502093)
            ·
              refine ⟨3160589513092260134063285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8428238701579360357502093 3160589513092260134063285)
              ·
                refine ⟨296305266852399387568433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3160589513092260134063285 296305266852399387568433)
                ·
                  refine ⟨222228950139299540676325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296305266852399387568433 222228950139299540676325)
                  ·
                    refine ⟨41667928151118663876811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 222228950139299540676325 41667928151118663876811)
                    ·
                      rfl

theorem cell22_121722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_121722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121722 prefixEnd_121722 := by exact prefixLift 121722
  have htrace : WordTrace (prefixWord ++ tailWord_121722) baseStart_121722 baseEnd_121722 := by
    simpa [prefixWord, tailWord_121722, baseEnd_121722] using wordTrace_append hprefix tailTrace_121722
  have hstable : (prefixWord ++ tailWord_121722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121722).length < 2 ^ (prefixWord ++ tailWord_121722).sum := by decide
  have hdescent : baseEnd_121722 < baseStart_121722 := by decide
  rcases family_descends (prefixWord ++ tailWord_121722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121737 : List Nat := [1, 2, 1, 1, 5, 4, 8]
def baseStart_121737 : Nat := 118140960795 + 121737 * 2 ^ 59
def prefixEnd_121737 : Nat := 4983230072969 + 3 ^ 40 * 121737 * 2
def baseEnd_121737 : Nat := 1543446776209763879695

theorem tailTrace_121737 : CollatzResearch.WordTrace tailWord_121737 prefixEnd_121737 1543446776209763879695 := by
  unfold tailWord_121737
  simp only [CollatzResearch.WordTrace]
  refine ⟨4440113159975114869451465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2960075439983409912967643 4440113159975114869451465)
  ·
    refine ⟨3330084869981336152088599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4440113159975114869451465 3330084869981336152088599)
    ·
      refine ⟨4995127304972004228132899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3330084869981336152088599 4995127304972004228132899)
      ·
        refine ⟨7492690957458006342199349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4995127304972004228132899 7492690957458006342199349)
        ·
          refine ⟨702439777261688094581189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7492690957458006342199349 702439777261688094581189)
          ·
            refine ⟨131707458236566517733973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 702439777261688094581189 131707458236566517733973)
            ·
              refine ⟨1543446776209763879695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 131707458236566517733973 1543446776209763879695)
              ·
                rfl

theorem cell22_121737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 8].length) (baseStart_121737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121737 prefixEnd_121737 := by exact prefixLift 121737
  have htrace : WordTrace (prefixWord ++ tailWord_121737) baseStart_121737 baseEnd_121737 := by
    simpa [prefixWord, tailWord_121737, baseEnd_121737] using wordTrace_append hprefix tailTrace_121737
  have hstable : (prefixWord ++ tailWord_121737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121737).length < 2 ^ (prefixWord ++ tailWord_121737).sum := by decide
  have hdescent : baseEnd_121737 < baseStart_121737 := by decide
  rcases family_descends (prefixWord ++ tailWord_121737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121754 : List Nat := [3, 1, 1, 4, 3, 1, 2, 7]
def baseStart_121754 : Nat := 118140960795 + 121754 * 2 ^ 59
def prefixEnd_121754 : Nat := 4983230072969 + 3 ^ 40 * 121754 * 2
def baseEnd_121754 : Nat := 4630986933897916341857

theorem tailTrace_121754 : CollatzResearch.WordTrace tailWord_121754 prefixEnd_121754 4630986933897916341857 := by
  unfold tailWord_121754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1110183300228381693205079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2960488800609017848546877 1110183300228381693205079)
  ·
    refine ⟨1665274950342572539807619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1110183300228381693205079 1665274950342572539807619)
    ·
      refine ⟨2497912425513858809711429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1665274950342572539807619 2497912425513858809711429)
      ·
        refine ⟨468358579783848526820893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2497912425513858809711429 468358579783848526820893)
        ·
          refine ⟨175634467418943197557835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 468358579783848526820893 175634467418943197557835)
          ·
            refine ⟨263451701128414796336753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175634467418943197557835 263451701128414796336753)
            ·
              refine ⟨197588775846311097252565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263451701128414796336753 197588775846311097252565)
              ·
                refine ⟨4630986933897916341857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 197588775846311097252565 4630986933897916341857)
                ·
                  rfl

theorem cell22_121754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 7].length) (baseStart_121754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121754 prefixEnd_121754 := by exact prefixLift 121754
  have htrace : WordTrace (prefixWord ++ tailWord_121754) baseStart_121754 baseEnd_121754 := by
    simpa [prefixWord, tailWord_121754, baseEnd_121754] using wordTrace_append hprefix tailTrace_121754
  have hstable : (prefixWord ++ tailWord_121754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121754).length < 2 ^ (prefixWord ++ tailWord_121754).sum := by decide
  have hdescent : baseEnd_121754 < baseStart_121754 := by decide
  rcases family_descends (prefixWord ++ tailWord_121754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121773 : List Nat := [1, 5, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_121773 : Nat := 118140960795 + 121773 * 2 ^ 59
def prefixEnd_121773 : Nat := 4983230072969 + 3 ^ 40 * 121773 * 2
def baseEnd_121773 : Nat := 41685386493371530851655

theorem tailTrace_121773 : CollatzResearch.WordTrace tailWord_121773 prefixEnd_121773 41685386493371530851655 := by
  unfold tailWord_121773
  simp only [CollatzResearch.WordTrace]
  refine ⟨4441426187844693017761973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2960950791896462011841315 4441426187844693017761973)
  ·
    refine ⟨416383705110439970415185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4441426187844693017761973 416383705110439970415185)
    ·
      refine ⟨312287778832829977811389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416383705110439970415185 312287778832829977811389)
      ·
        refine ⟨117107917062311241679271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312287778832829977811389 117107917062311241679271)
        ·
          refine ⟨175661875593466862518907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117107917062311241679271 175661875593466862518907)
          ·
            refine ⟨263492813390200293778361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175661875593466862518907 263492813390200293778361)
            ·
              refine ⟨197619610042650220333771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263492813390200293778361 197619610042650220333771)
              ·
                refine ⟨296429415063975330500657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197619610042650220333771 296429415063975330500657)
                ·
                  refine ⟨222322061297981497875493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296429415063975330500657 222322061297981497875493)
                  ·
                    refine ⟨41685386493371530851655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 222322061297981497875493 41685386493371530851655)
                    ·
                      rfl

theorem cell22_121773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_121773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121773 prefixEnd_121773 := by exact prefixLift 121773
  have htrace : WordTrace (prefixWord ++ tailWord_121773) baseStart_121773 baseEnd_121773 := by
    simpa [prefixWord, tailWord_121773, baseEnd_121773] using wordTrace_append hprefix tailTrace_121773
  have hstable : (prefixWord ++ tailWord_121773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121773).length < 2 ^ (prefixWord ++ tailWord_121773).sum := by decide
  have hdescent : baseEnd_121773 < baseStart_121773 := by decide
  rcases family_descends (prefixWord ++ tailWord_121773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121786 : List Nat := [3, 1, 1, 1, 2, 1, 4, 5, 1, 3]
def baseStart_121786 : Nat := 118140960795 + 121786 * 2 ^ 59
def prefixEnd_121786 : Nat := 4983230072969 + 3 ^ 40 * 121786 * 2
def baseEnd_121786 : Nat := 41689836659043830276615

theorem tailTrace_121786 : CollatzResearch.WordTrace tailWord_121786 prefixEnd_121786 41689836659043830276615 := by
  unfold tailWord_121786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1110475084199399059496303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2961266891198397491990141 1110475084199399059496303)
  ·
    refine ⟨1665712626299098589244455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1110475084199399059496303 1665712626299098589244455)
    ·
      refine ⟨2498568939448647883866683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1665712626299098589244455 2498568939448647883866683)
      ·
        refine ⟨3747853409172971825800025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2498568939448647883866683 3747853409172971825800025)
        ·
          refine ⟨2810890056879728869350019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3747853409172971825800025 2810890056879728869350019)
          ·
            refine ⟨4216335085319593304025029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810890056879728869350019 4216335085319593304025029)
            ·
              refine ⟨790562828497423744504693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4216335085319593304025029 790562828497423744504693)
              ·
                refine ⟨74115265171633476047315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 790562828497423744504693 74115265171633476047315)
                ·
                  refine ⟨111172897757450214070973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74115265171633476047315 111172897757450214070973)
                  ·
                    refine ⟨41689836659043830276615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111172897757450214070973 41689836659043830276615)
                    ·
                      rfl

theorem cell22_121786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 1, 3].length) (baseStart_121786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121786 prefixEnd_121786 := by exact prefixLift 121786
  have htrace : WordTrace (prefixWord ++ tailWord_121786) baseStart_121786 baseEnd_121786 := by
    simpa [prefixWord, tailWord_121786, baseEnd_121786] using wordTrace_append hprefix tailTrace_121786
  have hstable : (prefixWord ++ tailWord_121786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121786).length < 2 ^ (prefixWord ++ tailWord_121786).sum := by decide
  have hdescent : baseEnd_121786 < baseStart_121786 := by decide
  rcases family_descends (prefixWord ++ tailWord_121786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121803 : List Nat := [1, 1, 1, 1, 3, 5, 4, 2, 1, 3]
def baseStart_121803 : Nat := 118140960795 + 121803 * 2 ^ 59
def prefixEnd_121803 : Nat := 4983230072969 + 3 ^ 40 * 121803 * 2
def baseEnd_121803 : Nat := 41695656106461452601563

theorem tailTrace_121803 : CollatzResearch.WordTrace tailWord_121803 prefixEnd_121803 41695656106461452601563 := by
  unfold tailWord_121803
  simp only [CollatzResearch.WordTrace]
  refine ⟨4442520377736008141354063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2961680251824005427569375 4442520377736008141354063)
  ·
    refine ⟨6663780566604012212031095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4442520377736008141354063 6663780566604012212031095)
    ·
      refine ⟨9995670849906018318046643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6663780566604012212031095 9995670849906018318046643)
      ·
        refine ⟨14993506274859027477069965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9995670849906018318046643 14993506274859027477069965)
        ·
          refine ⟨5622564853072135303901237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14993506274859027477069965 5622564853072135303901237)
          ·
            refine ⟨527115454975512684740741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5622564853072135303901237 527115454975512684740741)
            ·
              refine ⟨98834147807908628388889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 527115454975512684740741 98834147807908628388889)
              ·
                refine ⟨74125610855931471291667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98834147807908628388889 74125610855931471291667)
                ·
                  refine ⟨111188416283897206937501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74125610855931471291667 111188416283897206937501)
                  ·
                    refine ⟨41695656106461452601563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111188416283897206937501 41695656106461452601563)
                    ·
                      rfl

theorem cell22_121803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 1, 3].length) (baseStart_121803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121803 prefixEnd_121803 := by exact prefixLift 121803
  have htrace : WordTrace (prefixWord ++ tailWord_121803) baseStart_121803 baseEnd_121803 := by
    simpa [prefixWord, tailWord_121803, baseEnd_121803] using wordTrace_append hprefix tailTrace_121803
  have hstable : (prefixWord ++ tailWord_121803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121803).length < 2 ^ (prefixWord ++ tailWord_121803).sum := by decide
  have hdescent : baseEnd_121803 < baseStart_121803 := by decide
  rcases family_descends (prefixWord ++ tailWord_121803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121805 : List Nat := [1, 6, 3, 1, 1, 2, 1, 7]
def baseStart_121805 : Nat := 118140960795 + 121805 * 2 ^ 59
def prefixEnd_121805 : Nat := 4983230072969 + 3 ^ 40 * 121805 * 2
def baseEnd_121805 : Nat := 4632926749703790450173

theorem tailTrace_121805 : CollatzResearch.WordTrace tailWord_121805 prefixEnd_121805 4632926749703790450173 := by
  unfold tailWord_121805
  simp only [CollatzResearch.WordTrace]
  refine ⟨4442593323728762482926869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2961728882485841655284579 4442593323728762482926869)
  ·
    refine ⟨208246562049785741387197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4442593323728762482926869 208246562049785741387197)
    ·
      refine ⟨78092460768669653020199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208246562049785741387197 78092460768669653020199)
      ·
        refine ⟨117138691153004479530299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78092460768669653020199 117138691153004479530299)
        ·
          refine ⟨175708036729506719295449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117138691153004479530299 175708036729506719295449)
          ·
            refine ⟨131781027547130039471587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175708036729506719295449 131781027547130039471587)
            ·
              refine ⟨197671541320695059207381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131781027547130039471587 197671541320695059207381)
              ·
                refine ⟨4632926749703790450173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 197671541320695059207381 4632926749703790450173)
                ·
                  rfl

theorem cell22_121805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 7].length) (baseStart_121805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121805 prefixEnd_121805 := by exact prefixLift 121805
  have htrace : WordTrace (prefixWord ++ tailWord_121805) baseStart_121805 baseEnd_121805 := by
    simpa [prefixWord, tailWord_121805, baseEnd_121805] using wordTrace_append hprefix tailTrace_121805
  have hstable : (prefixWord ++ tailWord_121805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121805).length < 2 ^ (prefixWord ++ tailWord_121805).sum := by decide
  have hdescent : baseEnd_121805 < baseStart_121805 := by decide
  rcases family_descends (prefixWord ++ tailWord_121805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121889 : List Nat := [1, 2, 3, 2, 3, 2, 1, 8]
def baseStart_121889 : Nat := 118140960795 + 121889 * 2 ^ 59
def prefixEnd_121889 : Nat := 4983230072969 + 3 ^ 40 * 121889 * 2
def baseEnd_121889 : Nat := 4636121740442877216811

theorem tailTrace_121889 : CollatzResearch.WordTrace tailWord_121889 prefixEnd_121889 4636121740442877216811 := by
  unfold tailWord_121889
  simp only [CollatzResearch.WordTrace]
  refine ⟨4445657055424444828984721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2963771370282963219323147 4445657055424444828984721)
  ·
    refine ⟨3334242791568333621738541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4445657055424444828984721 3334242791568333621738541)
    ·
      refine ⟨1250341046838125108151953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3334242791568333621738541 1250341046838125108151953)
      ·
        refine ⟨937755785128593831113965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1250341046838125108151953 937755785128593831113965)
        ·
          refine ⟨351658419423222686667737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 937755785128593831113965 351658419423222686667737)
          ·
            refine ⟨263743814567417015000803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351658419423222686667737 263743814567417015000803)
            ·
              refine ⟨395615721851125522501205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263743814567417015000803 395615721851125522501205)
              ·
                refine ⟨4636121740442877216811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 395615721851125522501205 4636121740442877216811)
                ·
                  rfl

theorem cell22_121889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 8].length) (baseStart_121889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121889 prefixEnd_121889 := by exact prefixLift 121889
  have htrace : WordTrace (prefixWord ++ tailWord_121889) baseStart_121889 baseEnd_121889 := by
    simpa [prefixWord, tailWord_121889, baseEnd_121889] using wordTrace_append hprefix tailTrace_121889
  have hstable : (prefixWord ++ tailWord_121889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121889).length < 2 ^ (prefixWord ++ tailWord_121889).sum := by decide
  have hdescent : baseEnd_121889 < baseStart_121889 := by decide
  rcases family_descends (prefixWord ++ tailWord_121889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121895 : List Nat := [1, 1, 7, 1, 1, 3, 1, 3, 4]
def baseStart_121895 : Nat := 118140960795 + 121895 * 2 ^ 59
def prefixEnd_121895 : Nat := 4983230072969 + 3 ^ 40 * 121895 * 2
def baseEnd_121895 : Nat := 13909049862201293100427

theorem tailTrace_121895 : CollatzResearch.WordTrace tailWord_121895 prefixEnd_121895 13909049862201293100427 := by
  unfold tailWord_121895
  simp only [CollatzResearch.WordTrace]
  refine ⟨4445875893402707853703139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2963917262268471902468759 4445875893402707853703139)
  ·
    refine ⟨6668813840104061780554709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4445875893402707853703139 6668813840104061780554709)
    ·
      refine ⟨156300324377438947981751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 6668813840104061780554709 156300324377438947981751)
      ·
        refine ⟨234450486566158421972627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156300324377438947981751 234450486566158421972627)
        ·
          refine ⟨351675729849237632958941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234450486566158421972627 351675729849237632958941)
          ·
            refine ⟨131878398693464112359603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351675729849237632958941 131878398693464112359603)
            ·
              refine ⟨197817598040196168539405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131878398693464112359603 197817598040196168539405)
              ·
                refine ⟨74181599265073563202277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197817598040196168539405 74181599265073563202277)
                ·
                  refine ⟨13909049862201293100427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74181599265073563202277 13909049862201293100427)
                  ·
                    rfl

theorem cell22_121895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 4].length) (baseStart_121895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121895 prefixEnd_121895 := by exact prefixLift 121895
  have htrace : WordTrace (prefixWord ++ tailWord_121895) baseStart_121895 baseEnd_121895 := by
    simpa [prefixWord, tailWord_121895, baseEnd_121895] using wordTrace_append hprefix tailTrace_121895
  have hstable : (prefixWord ++ tailWord_121895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121895).length < 2 ^ (prefixWord ++ tailWord_121895).sum := by decide
  have hdescent : baseEnd_121895 < baseStart_121895 := by decide
  rcases family_descends (prefixWord ++ tailWord_121895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121908 : List Nat := [2, 5, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_121908 : Nat := 118140960795 + 121908 * 2 ^ 59
def prefixEnd_121908 : Nat := 4983230072969 + 3 ^ 40 * 121908 * 2
def baseEnd_121908 : Nat := 41731599752276178726241

theorem tailTrace_121908 : CollatzResearch.WordTrace tailWord_121908 prefixEnd_121908 41731599752276178726241 := by
  unfold tailWord_121908
  simp only [CollatzResearch.WordTrace]
  refine ⟨2223175021177805536963189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2964233361570407382617585 2223175021177805536963189)
  ·
    refine ⟨208422658235419269090299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2223175021177805536963189 208422658235419269090299)
    ·
      refine ⟨312633987353128903635449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208422658235419269090299 312633987353128903635449)
      ·
        refine ⟨234475490514846677726587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312633987353128903635449 234475490514846677726587)
        ·
          refine ⟨351713235772270016589881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234475490514846677726587 351713235772270016589881)
          ·
            refine ⟨263784926829202512442411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351713235772270016589881 263784926829202512442411)
            ·
              refine ⟨395677390243803768663617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263784926829202512442411 395677390243803768663617)
              ·
                refine ⟨296758042682852826497713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395677390243803768663617 296758042682852826497713)
                ·
                  refine ⟨222568532012139619873285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296758042682852826497713 222568532012139619873285)
                  ·
                    refine ⟨41731599752276178726241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 222568532012139619873285 41731599752276178726241)
                    ·
                      rfl

theorem cell22_121908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_121908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_121908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_121908 prefixEnd_121908 := by exact prefixLift 121908
  have htrace : WordTrace (prefixWord ++ tailWord_121908) baseStart_121908 baseEnd_121908 := by
    simpa [prefixWord, tailWord_121908, baseEnd_121908] using wordTrace_append hprefix tailTrace_121908
  have hstable : (prefixWord ++ tailWord_121908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121908).length < 2 ^ (prefixWord ++ tailWord_121908).sum := by decide
  have hdescent : baseEnd_121908 < baseStart_121908 := by decide
  rcases family_descends (prefixWord ++ tailWord_121908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122013 : List Nat := [1, 4, 2, 1, 1, 2, 4, 3, 4]
def baseStart_122013 : Nat := 118140960795 + 122013 * 2 ^ 59
def prefixEnd_122013 : Nat := 4983230072969 + 3 ^ 40 * 122013 * 2
def baseEnd_122013 : Nat := 13922514466030301616973

theorem tailTrace_122013 : CollatzResearch.WordTrace tailWord_122013 prefixEnd_122013 13922514466030301616973 := by
  unfold tailWord_122013
  simp only [CollatzResearch.WordTrace]
  refine ⟨4450179706975214006498693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2966786471316809337665795 4450179706975214006498693)
  ·
    refine ⟨834408695057852626218505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4450179706975214006498693 834408695057852626218505)
    ·
      refine ⟨625806521293389469663879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 834408695057852626218505 625806521293389469663879)
      ·
        refine ⟨938709781940084204495819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625806521293389469663879 938709781940084204495819)
        ·
          refine ⟨1408064672910126306743729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938709781940084204495819 1408064672910126306743729)
          ·
            refine ⟨1056048504682594730057797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1408064672910126306743729 1056048504682594730057797)
            ·
              refine ⟨198009094627986511885837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1056048504682594730057797 198009094627986511885837)
              ·
                refine ⟨74253410485494941957189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198009094627986511885837 74253410485494941957189)
                ·
                  refine ⟨13922514466030301616973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74253410485494941957189 13922514466030301616973)
                  ·
                    rfl

theorem cell22_122013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_122013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122013 prefixEnd_122013 := by exact prefixLift 122013
  have htrace : WordTrace (prefixWord ++ tailWord_122013) baseStart_122013 baseEnd_122013 := by
    simpa [prefixWord, tailWord_122013, baseEnd_122013] using wordTrace_append hprefix tailTrace_122013
  have hstable : (prefixWord ++ tailWord_122013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122013).length < 2 ^ (prefixWord ++ tailWord_122013).sum := by decide
  have hdescent : baseEnd_122013 < baseStart_122013 := by decide
  rcases family_descends (prefixWord ++ tailWord_122013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122058 : List Nat := [3, 1, 2, 1, 3, 4, 2, 6]
def baseStart_122058 : Nat := 118140960795 + 122058 * 2 ^ 59
def prefixEnd_122058 : Nat := 4983230072969 + 3 ^ 40 * 122058 * 2
def baseEnd_122058 : Nat := 4642549757525087497309

theorem tailTrace_122058 : CollatzResearch.WordTrace tailWord_122058 prefixEnd_122058 4642549757525087497309 := by
  unfold tailWord_122058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1112955247953046672971707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2967880661208124461257885 1112955247953046672971707)
  ·
    refine ⟨1669432871929570009457561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1112955247953046672971707 1669432871929570009457561)
    ·
      refine ⟨1252074653947177507093171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1669432871929570009457561 1252074653947177507093171)
      ·
        refine ⟨1878111980920766260639757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1252074653947177507093171 1878111980920766260639757)
        ·
          refine ⟨704291992845287347739909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1878111980920766260639757 704291992845287347739909)
          ·
            refine ⟨132054748658491377701233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 704291992845287347739909 132054748658491377701233)
            ·
              refine ⟨99041061493868533275925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132054748658491377701233 99041061493868533275925)
              ·
                refine ⟨4642549757525087497309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99041061493868533275925 4642549757525087497309)
                ·
                  rfl

theorem cell22_122058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 6].length) (baseStart_122058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122058 prefixEnd_122058 := by exact prefixLift 122058
  have htrace : WordTrace (prefixWord ++ tailWord_122058) baseStart_122058 baseEnd_122058 := by
    simpa [prefixWord, tailWord_122058, baseEnd_122058] using wordTrace_append hprefix tailTrace_122058
  have hstable : (prefixWord ++ tailWord_122058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122058).length < 2 ^ (prefixWord ++ tailWord_122058).sum := by decide
  have hdescent : baseEnd_122058 < baseStart_122058 := by decide
  rcases family_descends (prefixWord ++ tailWord_122058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122090 : List Nat := [3, 1, 3, 1, 1, 5, 1, 1, 3, 3]
def baseStart_122090 : Nat := 118140960795 + 122090 * 2 ^ 59
def prefixEnd_122090 : Nat := 4983230072969 + 3 ^ 40 * 122090 * 2
def baseEnd_122090 : Nat := 41793902071688370675683

theorem tailTrace_122090 : CollatzResearch.WordTrace tailWord_122090 prefixEnd_122090 41793902071688370675683 := by
  unfold tailWord_122090
  simp only [CollatzResearch.WordTrace]
  refine ⟨1113247031924064039262931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2968658751797504104701149 1113247031924064039262931)
  ·
    refine ⟨1669870547886096058894397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1113247031924064039262931 1669870547886096058894397)
    ·
      refine ⟨626201455457286022085399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1669870547886096058894397 626201455457286022085399)
      ·
        refine ⟨939302183185929033128099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626201455457286022085399 939302183185929033128099)
        ·
          refine ⟨1408953274778893549692149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939302183185929033128099 1408953274778893549692149)
          ·
            refine ⟨132089369510521270283639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1408953274778893549692149 132089369510521270283639)
            ·
              refine ⟨198134054265781905425459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132089369510521270283639 198134054265781905425459)
              ·
                refine ⟨297201081398672858138189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198134054265781905425459 297201081398672858138189)
                ·
                  refine ⟨111450405524502321801821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297201081398672858138189 111450405524502321801821)
                  ·
                    refine ⟨41793902071688370675683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111450405524502321801821 41793902071688370675683)
                    ·
                      rfl

theorem cell22_122090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_122090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122090 prefixEnd_122090 := by exact prefixLift 122090
  have htrace : WordTrace (prefixWord ++ tailWord_122090) baseStart_122090 baseEnd_122090 := by
    simpa [prefixWord, tailWord_122090, baseEnd_122090] using wordTrace_append hprefix tailTrace_122090
  have hstable : (prefixWord ++ tailWord_122090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122090).length < 2 ^ (prefixWord ++ tailWord_122090).sum := by decide
  have hdescent : baseEnd_122090 < baseStart_122090 := by decide
  rcases family_descends (prefixWord ++ tailWord_122090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122163 : List Nat := [1, 1, 1, 2, 5, 3, 2, 1, 1, 5]
def baseStart_122163 : Nat := 118140960795 + 122163 * 2 ^ 59
def prefixEnd_122163 : Nat := 4983230072969 + 3 ^ 40 * 122163 * 2
def baseEnd_122163 : Nat := 41818891463540513600459

theorem tailTrace_122163 : CollatzResearch.WordTrace tailWord_122163 prefixEnd_122163 41818891463540513600459 := by
  unfold tailWord_122163
  simp only [CollatzResearch.WordTrace]
  refine ⟨4455650656431789624459143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2970433770954526416306095 4455650656431789624459143)
  ·
    refine ⟨6683475984647684436688715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4455650656431789624459143 6683475984647684436688715)
    ·
      refine ⟨10025213976971526655033073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6683475984647684436688715 10025213976971526655033073)
      ·
        refine ⟨7518910482728644991274805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10025213976971526655033073 7518910482728644991274805)
        ·
          refine ⟨704897857755810467932013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7518910482728644991274805 704897857755810467932013)
          ·
            refine ⟨264336696658428925474505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 704897857755810467932013 264336696658428925474505)
            ·
              refine ⟨198252522493821694105879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264336696658428925474505 198252522493821694105879)
              ·
                refine ⟨297378783740732541158819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198252522493821694105879 297378783740732541158819)
                ·
                  refine ⟨446068175611098811738229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297378783740732541158819 446068175611098811738229)
                  ·
                    refine ⟨41818891463540513600459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 446068175611098811738229 41818891463540513600459)
                    ·
                      rfl

theorem cell22_122163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 5].length) (baseStart_122163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122163 prefixEnd_122163 := by exact prefixLift 122163
  have htrace : WordTrace (prefixWord ++ tailWord_122163) baseStart_122163 baseEnd_122163 := by
    simpa [prefixWord, tailWord_122163, baseEnd_122163] using wordTrace_append hprefix tailTrace_122163
  have hstable : (prefixWord ++ tailWord_122163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122163).length < 2 ^ (prefixWord ++ tailWord_122163).sum := by decide
  have hdescent : baseEnd_122163 < baseStart_122163 := by decide
  rcases family_descends (prefixWord ++ tailWord_122163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122180 : List Nat := [2, 3, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_122180 : Nat := 118140960795 + 122180 * 2 ^ 59
def prefixEnd_122180 : Nat := 4983230072969 + 3 ^ 40 * 122180 * 2
def baseEnd_122180 : Nat := 41824710910958135925407

theorem tailTrace_122180 : CollatzResearch.WordTrace tailWord_122180 prefixEnd_122180 41824710910958135925407 := by
  unfold tailWord_122180
  simp only [CollatzResearch.WordTrace]
  refine ⟨2228135348685100763913997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2970847131580134351885329 2228135348685100763913997)
  ·
    refine ⟨835550755756912786467749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2228135348685100763913997 835550755756912786467749)
    ·
      refine ⟨156665766704421147462703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 835550755756912786467749 156665766704421147462703)
      ·
        refine ⟨234998650056631721194055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156665766704421147462703 234998650056631721194055)
        ·
          refine ⟨352497975084947581791083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234998650056631721194055 352497975084947581791083)
          ·
            refine ⟨528746962627421372686625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352497975084947581791083 528746962627421372686625)
            ·
              refine ⟨396560221970566029514969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528746962627421372686625 396560221970566029514969)
              ·
                refine ⟨297420166477924522136227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396560221970566029514969 297420166477924522136227)
                ·
                  refine ⟨446130249716886783204341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297420166477924522136227 446130249716886783204341)
                  ·
                    refine ⟨41824710910958135925407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 446130249716886783204341 41824710910958135925407)
                    ·
                      rfl

theorem cell22_122180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_122180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122180 prefixEnd_122180 := by exact prefixLift 122180
  have htrace : WordTrace (prefixWord ++ tailWord_122180) baseStart_122180 baseEnd_122180 := by
    simpa [prefixWord, tailWord_122180, baseEnd_122180] using wordTrace_append hprefix tailTrace_122180
  have hstable : (prefixWord ++ tailWord_122180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122180).length < 2 ^ (prefixWord ++ tailWord_122180).sum := by decide
  have hdescent : baseEnd_122180 < baseStart_122180 := by decide
  rcases family_descends (prefixWord ++ tailWord_122180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122197 : List Nat := [1, 3, 2, 2, 3, 3, 1, 2, 2, 3]
def baseStart_122197 : Nat := 118140960795 + 122197 * 2 ^ 59
def prefixEnd_122197 : Nat := 4983230072969 + 3 ^ 40 * 122197 * 2
def baseEnd_122197 : Nat := 41830530358375758250355

theorem tailTrace_122197 : CollatzResearch.WordTrace tailWord_122197 prefixEnd_122197 41830530358375758250355 := by
  unfold tailWord_122197
  simp only [CollatzResearch.WordTrace]
  refine ⟨4456890738308613431196845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2971260492205742287464563 4456890738308613431196845)
  ·
    refine ⟨1671334026865730036698817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4456890738308613431196845 1671334026865730036698817)
    ·
      refine ⟨1253500520149297527524113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1671334026865730036698817 1253500520149297527524113)
      ·
        refine ⟨940125390111973145643085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1253500520149297527524113 940125390111973145643085)
        ·
          refine ⟨352547021291989929616157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 940125390111973145643085 352547021291989929616157)
          ·
            refine ⟨132205132984496223606059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352547021291989929616157 132205132984496223606059)
            ·
              refine ⟨198307699476744335409089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132205132984496223606059 198307699476744335409089)
              ·
                refine ⟨148730774607558251556817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198307699476744335409089 148730774607558251556817)
                ·
                  refine ⟨111548080955668688667613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148730774607558251556817 111548080955668688667613)
                  ·
                    refine ⟨41830530358375758250355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111548080955668688667613 41830530358375758250355)
                    ·
                      rfl

theorem cell22_122197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_122197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122197 prefixEnd_122197 := by exact prefixLift 122197
  have htrace : WordTrace (prefixWord ++ tailWord_122197) baseStart_122197 baseEnd_122197 := by
    simpa [prefixWord, tailWord_122197, baseEnd_122197] using wordTrace_append hprefix tailTrace_122197
  have hstable : (prefixWord ++ tailWord_122197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122197).length < 2 ^ (prefixWord ++ tailWord_122197).sum := by decide
  have hdescent : baseEnd_122197 < baseStart_122197 := by decide
  rcases family_descends (prefixWord ++ tailWord_122197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122315 : List Nat := [1, 1, 1, 1, 3, 3, 3, 4, 2, 3]
def baseStart_122315 : Nat := 118140960795 + 122315 * 2 ^ 59
def prefixEnd_122315 : Nat := 4983230072969 + 3 ^ 40 * 122315 * 2
def baseEnd_122315 : Nat := 41870924169862783799993

theorem tailTrace_122315 : CollatzResearch.WordTrace tailWord_122315 prefixEnd_122315 41870924169862783799993 := by
  unfold tailWord_122315
  simp only [CollatzResearch.WordTrace]
  refine ⟨4461194551881119583992399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2974129701254079722661599 4461194551881119583992399)
  ·
    refine ⟨6691791827821679375988599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4461194551881119583992399 6691791827821679375988599)
    ·
      refine ⟨10037687741732519063982899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6691791827821679375988599 10037687741732519063982899)
      ·
        refine ⟨15056531612598778595974349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10037687741732519063982899 15056531612598778595974349)
        ·
          refine ⟨5646199354724541973490381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15056531612598778595974349 5646199354724541973490381)
          ·
            refine ⟨2117324758021703240058893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5646199354724541973490381 2117324758021703240058893)
            ·
              refine ⟨793996784258138715022085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2117324758021703240058893 793996784258138715022085)
              ·
                refine ⟨148874397048401009066641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 793996784258138715022085 148874397048401009066641)
                ·
                  refine ⟨111655797786300756799981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148874397048401009066641 111655797786300756799981)
                  ·
                    refine ⟨41870924169862783799993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111655797786300756799981 41870924169862783799993)
                    ·
                      rfl

theorem cell22_122315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 3].length) (baseStart_122315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122315 prefixEnd_122315 := by exact prefixLift 122315
  have htrace : WordTrace (prefixWord ++ tailWord_122315) baseStart_122315 baseEnd_122315 := by
    simpa [prefixWord, tailWord_122315, baseEnd_122315] using wordTrace_append hprefix tailTrace_122315
  have hstable : (prefixWord ++ tailWord_122315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122315).length < 2 ^ (prefixWord ++ tailWord_122315).sum := by decide
  have hdescent : baseEnd_122315 < baseStart_122315 := by decide
  rcases family_descends (prefixWord ++ tailWord_122315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122328 : List Nat := [2, 1, 2, 2, 2, 1, 5, 7]
def baseStart_122328 : Nat := 118140960795 + 122328 * 2 ^ 59
def prefixEnd_122328 : Nat := 4983230072969 + 3 ^ 40 * 122328 * 2
def baseEnd_122328 : Nat := 4652819370615009247217

theorem tailTrace_122328 : CollatzResearch.WordTrace tailWord_122328 prefixEnd_122328 4652819370615009247217 := by
  unfold tailWord_122328
  simp only [CollatzResearch.WordTrace]
  refine ⟨2230834350417011402107819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2974445800556015202810425 2230834350417011402107819)
  ·
    refine ⟨3346251525625517103161729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2230834350417011402107819 3346251525625517103161729)
    ·
      refine ⟨2509688644219137827371297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3346251525625517103161729 2509688644219137827371297)
      ·
        refine ⟨1882266483164353370528473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2509688644219137827371297 1882266483164353370528473)
        ·
          refine ⟨1411699862373265027896355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1882266483164353370528473 1411699862373265027896355)
          ·
            refine ⟨2117549793559897541844533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411699862373265027896355 2117549793559897541844533)
            ·
              refine ⟨198520293146240394547925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2117549793559897541844533 198520293146240394547925)
              ·
                refine ⟨4652819370615009247217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 198520293146240394547925 4652819370615009247217)
                ·
                  rfl

theorem cell22_122328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 7].length) (baseStart_122328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122328 prefixEnd_122328 := by exact prefixLift 122328
  have htrace : WordTrace (prefixWord ++ tailWord_122328) baseStart_122328 baseEnd_122328 := by
    simpa [prefixWord, tailWord_122328, baseEnd_122328] using wordTrace_append hprefix tailTrace_122328
  have hstable : (prefixWord ++ tailWord_122328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122328).length < 2 ^ (prefixWord ++ tailWord_122328).sum := by decide
  have hdescent : baseEnd_122328 < baseStart_122328 := by decide
  rcases family_descends (prefixWord ++ tailWord_122328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122377 : List Nat := [1, 2, 1, 1, 3, 1, 3, 6, 1, 3]
def baseStart_122377 : Nat := 118140960795 + 122377 * 2 ^ 59
def prefixEnd_122377 : Nat := 4983230072969 + 3 ^ 40 * 122377 * 2
def baseEnd_122377 : Nat := 41892148036915288749803

theorem tailTrace_122377 : CollatzResearch.WordTrace tailWord_122377 prefixEnd_122377 41892148036915288749803 := by
  unfold tailWord_122377
  simp only [CollatzResearch.WordTrace]
  refine ⟨4463455877656504172749385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2975637251771002781832923 4463455877656504172749385)
  ·
    refine ⟨3347591908242378129562039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4463455877656504172749385 3347591908242378129562039)
    ·
      refine ⟨5021387862363567194343059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3347591908242378129562039 5021387862363567194343059)
      ·
        refine ⟨7532081793545350791514589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5021387862363567194343059 7532081793545350791514589)
        ·
          refine ⟨2824530672579506546817971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7532081793545350791514589 2824530672579506546817971)
          ·
            refine ⟨4236796008869259820226957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824530672579506546817971 4236796008869259820226957)
            ·
              refine ⟨1588798503325972432585109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4236796008869259820226957 1588798503325972432585109)
              ·
                refine ⟨74474929843404957777427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1588798503325972432585109 74474929843404957777427)
                ·
                  refine ⟨111712394765107436666141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74474929843404957777427 111712394765107436666141)
                  ·
                    refine ⟨41892148036915288749803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111712394765107436666141 41892148036915288749803)
                    ·
                      rfl

theorem cell22_122377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 1, 3].length) (baseStart_122377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122377 prefixEnd_122377 := by exact prefixLift 122377
  have htrace : WordTrace (prefixWord ++ tailWord_122377) baseStart_122377 baseEnd_122377 := by
    simpa [prefixWord, tailWord_122377, baseEnd_122377] using wordTrace_append hprefix tailTrace_122377
  have hstable : (prefixWord ++ tailWord_122377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122377).length < 2 ^ (prefixWord ++ tailWord_122377).sum := by decide
  have hdescent : baseEnd_122377 < baseStart_122377 := by decide
  rcases family_descends (prefixWord ++ tailWord_122377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122482 : List Nat := [3, 2, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_122482 : Nat := 118140960795 + 122482 * 2 ^ 59
def prefixEnd_122482 : Nat := 4983230072969 + 3 ^ 40 * 122482 * 2
def baseEnd_122482 : Nat := 41928091682730014874481

theorem tailTrace_122482 : CollatzResearch.WordTrace tailWord_122482 prefixEnd_122482 41928091682730014874481 := by
  unfold tailWord_122482
  simp only [CollatzResearch.WordTrace]
  refine ⟨1116821385569026776330425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2978190361517404736881133 1116821385569026776330425)
  ·
    refine ⟨837616039176770082247819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1116821385569026776330425 837616039176770082247819)
    ·
      refine ⟨1256424058765155123371729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 837616039176770082247819 1256424058765155123371729)
      ·
        refine ⟨942318044073866342528797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1256424058765155123371729 942318044073866342528797)
        ·
          refine ⟨353369266527699878448299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 942318044073866342528797 353369266527699878448299)
          ·
            refine ⟨530053899791549817672449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353369266527699878448299 530053899791549817672449)
            ·
              refine ⟨397540424843662363254337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530053899791549817672449 397540424843662363254337)
              ·
                refine ⟨298155318632746772440753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397540424843662363254337 298155318632746772440753)
                ·
                  refine ⟨223616488974560079330565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298155318632746772440753 223616488974560079330565)
                  ·
                    refine ⟨41928091682730014874481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 223616488974560079330565 41928091682730014874481)
                    ·
                      rfl

theorem cell22_122482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_122482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122482 prefixEnd_122482 := by exact prefixLift 122482
  have htrace : WordTrace (prefixWord ++ tailWord_122482) baseStart_122482 baseEnd_122482 := by
    simpa [prefixWord, tailWord_122482, baseEnd_122482] using wordTrace_append hprefix tailTrace_122482
  have hstable : (prefixWord ++ tailWord_122482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122482).length < 2 ^ (prefixWord ++ tailWord_122482).sum := by decide
  have hdescent : baseEnd_122482 < baseStart_122482 := by decide
  rcases family_descends (prefixWord ++ tailWord_122482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122486 : List Nat := [5, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_122486 : Nat := 118140960795 + 122486 * 2 ^ 59
def prefixEnd_122486 : Nat := 4983230072969 + 3 ^ 40 * 122486 * 2
def baseEnd_122486 : Nat := 13976486988158445924823

theorem tailTrace_122486 : CollatzResearch.WordTrace tailWord_122486 prefixEnd_122486 13976486988158445924823 := by
  unfold tailWord_122486
  simp only [CollatzResearch.WordTrace]
  refine ⟨279214464641350986779207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2978287622841077192311541 279214464641350986779207)
  ·
    refine ⟨418821696962026480168811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279214464641350986779207 418821696962026480168811)
    ·
      refine ⟨628232545443039720253217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418821696962026480168811 628232545443039720253217)
      ·
        refine ⟨471174409082279790189913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628232545443039720253217 471174409082279790189913)
        ·
          refine ⟨353380806811709842642435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471174409082279790189913 353380806811709842642435)
          ·
            refine ⟨530071210217564763963653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353380806811709842642435 530071210217564763963653)
            ·
              refine ⟨99388351915793393243185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 530071210217564763963653 99388351915793393243185)
              ·
                refine ⟨74541263936845044932389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99388351915793393243185 74541263936845044932389)
                ·
                  refine ⟨13976486988158445924823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74541263936845044932389 13976486988158445924823)
                  ·
                    rfl

theorem cell22_122486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_122486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122486 prefixEnd_122486 := by exact prefixLift 122486
  have htrace : WordTrace (prefixWord ++ tailWord_122486) baseStart_122486 baseEnd_122486 := by
    simpa [prefixWord, tailWord_122486, baseEnd_122486] using wordTrace_append hprefix tailTrace_122486
  have hstable : (prefixWord ++ tailWord_122486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122486).length < 2 ^ (prefixWord ++ tailWord_122486).sum := by decide
  have hdescent : baseEnd_122486 < baseStart_122486 := by decide
  rcases family_descends (prefixWord ++ tailWord_122486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122497 : List Nat := [1, 2, 4, 2, 1, 4, 1, 7]
def baseStart_122497 : Nat := 118140960795 + 122497 * 2 ^ 59
def prefixEnd_122497 : Nat := 4983230072969 + 3 ^ 40 * 122497 * 2
def baseEnd_122497 : Nat := 4659247387697219527715

theorem tailTrace_122497 : CollatzResearch.WordTrace tailWord_122497 prefixEnd_122497 4659247387697219527715 := by
  unfold tailWord_122497
  simp only [CollatzResearch.WordTrace]
  refine ⟨4467832637221764667117745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2978555091481176444745163 4467832637221764667117745)
  ·
    refine ⟨3350874477916323500338309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4467832637221764667117745 3350874477916323500338309)
    ·
      refine ⟨628288964609310656313433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3350874477916323500338309 628288964609310656313433)
      ·
        refine ⟨471216723456982992235075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628288964609310656313433 471216723456982992235075)
        ·
          refine ⟨706825085185474488352613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471216723456982992235075 706825085185474488352613)
          ·
            refine ⟨132529703472276466566115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 706825085185474488352613 132529703472276466566115)
            ·
              refine ⟨198794555208414699849173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132529703472276466566115 198794555208414699849173)
              ·
                refine ⟨4659247387697219527715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 198794555208414699849173 4659247387697219527715)
                ·
                  rfl

theorem cell22_122497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 7].length) (baseStart_122497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122497 prefixEnd_122497 := by exact prefixLift 122497
  have htrace : WordTrace (prefixWord ++ tailWord_122497) baseStart_122497 baseEnd_122497 := by
    simpa [prefixWord, tailWord_122497, baseEnd_122497] using wordTrace_append hprefix tailTrace_122497
  have hstable : (prefixWord ++ tailWord_122497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122497).length < 2 ^ (prefixWord ++ tailWord_122497).sum := by decide
  have hdescent : baseEnd_122497 < baseStart_122497 := by decide
  rcases family_descends (prefixWord ++ tailWord_122497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122514 : List Nat := [3, 2, 3, 1, 3, 1, 3, 6]
def baseStart_122514 : Nat := 118140960795 + 122514 * 2 ^ 59
def prefixEnd_122514 : Nat := 4983230072969 + 3 ^ 40 * 122514 * 2
def baseEnd_122514 : Nat := 4659893992965844230487

theorem tailTrace_122514 : CollatzResearch.WordTrace tailWord_122514 prefixEnd_122514 4659893992965844230487 := by
  unfold tailWord_122514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1117113169540044142621649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2978968452106784380324397 1117113169540044142621649)
  ·
    refine ⟨837834877155033106966237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1117113169540044142621649 837834877155033106966237)
    ·
      refine ⟨314188078933137415112339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 837834877155033106966237 314188078933137415112339)
      ·
        refine ⟨471282118399706122668509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314188078933137415112339 471282118399706122668509)
        ·
          refine ⟨176730794399889796000691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 471282118399706122668509 176730794399889796000691)
          ·
            refine ⟨265096191599834694001037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176730794399889796000691 265096191599834694001037)
            ·
              refine ⟨99411071849938010250389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265096191599834694001037 99411071849938010250389)
              ·
                refine ⟨4659893992965844230487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99411071849938010250389 4659893992965844230487)
                ·
                  rfl

theorem cell22_122514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 6].length) (baseStart_122514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122514 prefixEnd_122514 := by exact prefixLift 122514
  have htrace : WordTrace (prefixWord ++ tailWord_122514) baseStart_122514 baseEnd_122514 := by
    simpa [prefixWord, tailWord_122514, baseEnd_122514] using wordTrace_append hprefix tailTrace_122514
  have hstable : (prefixWord ++ tailWord_122514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122514).length < 2 ^ (prefixWord ++ tailWord_122514).sum := by decide
  have hdescent : baseEnd_122514 < baseStart_122514 := by decide
  rcases family_descends (prefixWord ++ tailWord_122514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122516 : List Nat := [2, 4, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_122516 : Nat := 118140960795 + 122516 * 2 ^ 59
def prefixEnd_122516 : Nat := 4983230072969 + 3 ^ 40 * 122516 * 2
def baseEnd_122516 : Nat := 41939730577565259524377

theorem tailTrace_122516 : CollatzResearch.WordTrace tailWord_122516 prefixEnd_122516 41939730577565259524377 := by
  unfold tailWord_122516
  simp only [CollatzResearch.WordTrace]
  refine ⟨2234262812076465456029701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2979017082768620608039601 2234262812076465456029701)
  ·
    refine ⟨418924277264337273005569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2234262812076465456029701 418924277264337273005569)
    ·
      refine ⟨314193207948252954754177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418924277264337273005569 314193207948252954754177)
      ·
        refine ⟨235644905961189716065633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314193207948252954754177 235644905961189716065633)
        ·
          refine ⟨176733679470892287049225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235644905961189716065633 176733679470892287049225)
          ·
            refine ⟨132550259603169215286919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176733679470892287049225 132550259603169215286919)
            ·
              refine ⟨198825389404753822930379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132550259603169215286919 198825389404753822930379)
              ·
                refine ⟨298238084107130734395569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198825389404753822930379 298238084107130734395569)
                ·
                  refine ⟨223678563080348050796677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298238084107130734395569 223678563080348050796677)
                  ·
                    refine ⟨41939730577565259524377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 223678563080348050796677 41939730577565259524377)
                    ·
                      rfl

theorem cell22_122516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_122516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122516 prefixEnd_122516 := by exact prefixLift 122516
  have htrace : WordTrace (prefixWord ++ tailWord_122516) baseStart_122516 baseEnd_122516 := by
    simpa [prefixWord, tailWord_122516, baseEnd_122516] using wordTrace_append hprefix tailTrace_122516
  have hstable : (prefixWord ++ tailWord_122516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122516).length < 2 ^ (prefixWord ++ tailWord_122516).sum := by decide
  have hdescent : baseEnd_122516 < baseStart_122516 := by decide
  rcases family_descends (prefixWord ++ tailWord_122516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122525 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 7]
def baseStart_122525 : Nat := 118140960795 + 122525 * 2 ^ 59
def prefixEnd_122525 : Nat := 4983230072969 + 3 ^ 40 * 122525 * 2
def baseEnd_122525 : Nat := 13980937153830745349783

theorem tailTrace_122525 : CollatzResearch.WordTrace tailWord_122525 prefixEnd_122525 13980937153830745349783 := by
  unfold tailWord_122525
  simp only [CollatzResearch.WordTrace]
  refine ⟨4468853881120325449137029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2979235920746883632758019 4468853881120325449137029)
  ·
    refine ⟨837910102710061021713193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4468853881120325449137029 837910102710061021713193)
    ·
      refine ⟨628432577032545766284895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 837910102710061021713193 628432577032545766284895)
      ·
        refine ⟨942648865548818649427343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628432577032545766284895 942648865548818649427343)
        ·
          refine ⟨1413973298323227974141015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942648865548818649427343 1413973298323227974141015)
          ·
            refine ⟨2120959947484841961211523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413973298323227974141015 2120959947484841961211523)
            ·
              refine ⟨3181439921227262941817285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120959947484841961211523 3181439921227262941817285)
              ·
                refine ⟨596519985230111801590741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3181439921227262941817285 596519985230111801590741)
                ·
                  refine ⟨13980937153830745349783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 596519985230111801590741 13980937153830745349783)
                  ·
                    rfl

theorem cell22_122525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_122525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122525 prefixEnd_122525 := by exact prefixLift 122525
  have htrace : WordTrace (prefixWord ++ tailWord_122525) baseStart_122525 baseEnd_122525 := by
    simpa [prefixWord, tailWord_122525, baseEnd_122525] using wordTrace_append hprefix tailTrace_122525
  have hstable : (prefixWord ++ tailWord_122525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122525).length < 2 ^ (prefixWord ++ tailWord_122525).sum := by decide
  have hdescent : baseEnd_122525 < baseStart_122525 := by decide
  rcases family_descends (prefixWord ++ tailWord_122525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122555 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 5, 4]
def baseStart_122555 : Nat := 118140960795 + 122555 * 2 ^ 59
def prefixEnd_122555 : Nat := 4983230072969 + 3 ^ 40 * 122555 * 2
def baseEnd_122555 : Nat := 41953081074582157799257

theorem tailTrace_122555 : CollatzResearch.WordTrace tailWord_122555 prefixEnd_122555 41953081074582157799257 := by
  unfold tailWord_122555
  simp only [CollatzResearch.WordTrace]
  refine ⟨4469948071011640572729119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2979965380674427048486079 4469948071011640572729119)
  ·
    refine ⟨6704922106517460859093679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4469948071011640572729119 6704922106517460859093679)
    ·
      refine ⟨10057383159776191288640519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6704922106517460859093679 10057383159776191288640519)
      ·
        refine ⟨15086074739664286932960779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10057383159776191288640519 15086074739664286932960779)
        ·
          refine ⟨22629112109496430399441169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15086074739664286932960779 22629112109496430399441169)
          ·
            refine ⟨16971834082122322799580877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22629112109496430399441169 16971834082122322799580877)
            ·
              refine ⟨6364437780795871049842829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16971834082122322799580877 6364437780795871049842829)
              ·
                refine ⟨2386664167798451643691061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6364437780795871049842829 2386664167798451643691061)
                ·
                  refine ⟨223749765731104841596037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2386664167798451643691061 223749765731104841596037)
                  ·
                    refine ⟨41953081074582157799257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 223749765731104841596037 41953081074582157799257)
                    ·
                      rfl

theorem cell22_122555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 4].length) (baseStart_122555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122555 prefixEnd_122555 := by exact prefixLift 122555
  have htrace : WordTrace (prefixWord ++ tailWord_122555) baseStart_122555 baseEnd_122555 := by
    simpa [prefixWord, tailWord_122555, baseEnd_122555] using wordTrace_append hprefix tailTrace_122555
  have hstable : (prefixWord ++ tailWord_122555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122555).length < 2 ^ (prefixWord ++ tailWord_122555).sum := by decide
  have hdescent : baseEnd_122555 < baseStart_122555 := by decide
  rcases family_descends (prefixWord ++ tailWord_122555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122615 : List Nat := [1, 1, 3, 1, 1, 1, 5, 9]
def baseStart_122615 : Nat := 118140960795 + 122615 * 2 ^ 59
def prefixEnd_122615 : Nat := 4983230072969 + 3 ^ 40 * 122615 * 2
def baseEnd_122615 : Nat := 4663735588973555699897

theorem tailTrace_122615 : CollatzResearch.WordTrace tailWord_122615 prefixEnd_122615 4663735588973555699897 := by
  unfold tailWord_122615
  simp only [CollatzResearch.WordTrace]
  refine ⟨4472136450794270819913299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2981424300529513879942199 4472136450794270819913299)
  ·
    refine ⟨6708204676191406229869949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4472136450794270819913299 6708204676191406229869949)
    ·
      refine ⟨2515576753571777336201231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6708204676191406229869949 2515576753571777336201231)
      ·
        refine ⟨3773365130357666004301847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2515576753571777336201231 3773365130357666004301847)
        ·
          refine ⟨5660047695536499006452771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3773365130357666004301847 5660047695536499006452771)
          ·
            refine ⟨8490071543304748509679157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5660047695536499006452771 8490071543304748509679157)
            ·
              refine ⟨795944207184820172782421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8490071543304748509679157 795944207184820172782421)
              ·
                refine ⟨4663735588973555699897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 795944207184820172782421 4663735588973555699897)
                ·
                  rfl

theorem cell22_122615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 9].length) (baseStart_122615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122615 prefixEnd_122615 := by exact prefixLift 122615
  have htrace : WordTrace (prefixWord ++ tailWord_122615) baseStart_122615 baseEnd_122615 := by
    simpa [prefixWord, tailWord_122615, baseEnd_122615] using wordTrace_append hprefix tailTrace_122615
  have hstable : (prefixWord ++ tailWord_122615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122615).length < 2 ^ (prefixWord ++ tailWord_122615).sum := by decide
  have hdescent : baseEnd_122615 < baseStart_122615 := by decide
  rcases family_descends (prefixWord ++ tailWord_122615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122634 : List Nat := [3, 1, 2, 2, 1, 4, 2, 1, 2, 4]
def baseStart_122634 : Nat := 118140960795 + 122634 * 2 ^ 59
def prefixEnd_122634 : Nat := 4983230072969 + 3 ^ 40 * 122634 * 2
def baseEnd_122634 : Nat := 41980124389052285074015

theorem tailTrace_122634 : CollatzResearch.WordTrace tailWord_122634 prefixEnd_122634 41980124389052285074015 := by
  unfold tailWord_122634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1118207359431359266213739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2981886291816958043236637 1118207359431359266213739)
  ·
    refine ⟨1677311039147038899320609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1118207359431359266213739 1677311039147038899320609)
    ·
      refine ⟨1257983279360279174490457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1677311039147038899320609 1257983279360279174490457)
      ·
        refine ⟨943487459520209380867843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1257983279360279174490457 943487459520209380867843)
        ·
          refine ⟨1415231189280314071301765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943487459520209380867843 1415231189280314071301765)
          ·
            refine ⟨265355847990058888369081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1415231189280314071301765 265355847990058888369081)
            ·
              refine ⟨199016885992544166276811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265355847990058888369081 199016885992544166276811)
              ·
                refine ⟨298525328988816249415217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199016885992544166276811 298525328988816249415217)
                ·
                  refine ⟨223893996741612187061413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298525328988816249415217 223893996741612187061413)
                  ·
                    refine ⟨41980124389052285074015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 223893996741612187061413 41980124389052285074015)
                    ·
                      rfl

theorem cell22_122634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_122634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122634 prefixEnd_122634 := by exact prefixLift 122634
  have htrace : WordTrace (prefixWord ++ tailWord_122634) baseStart_122634 baseEnd_122634 := by
    simpa [prefixWord, tailWord_122634, baseEnd_122634] using wordTrace_append hprefix tailTrace_122634
  have hstable : (prefixWord ++ tailWord_122634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122634).length < 2 ^ (prefixWord ++ tailWord_122634).sum := by decide
  have hdescent : baseEnd_122634 < baseStart_122634 := by decide
  rcases family_descends (prefixWord ++ tailWord_122634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122711 : List Nat := [1, 1, 3, 2, 5, 2, 1, 2, 5]
def baseStart_122711 : Nat := 118140960795 + 122711 * 2 ^ 59
def prefixEnd_122711 : Nat := 4983230072969 + 3 ^ 40 * 122711 * 2
def baseEnd_122711 : Nat := 14002161020883250299593

theorem tailTrace_122711 : CollatzResearch.WordTrace tailWord_122711 prefixEnd_122711 14002161020883250299593 := by
  unfold tailWord_122711
  simp only [CollatzResearch.WordTrace]
  refine ⟨4475637858446479215407987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2983758572297652810271991 4475637858446479215407987)
  ·
    refine ⟨6713456787669718823111981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4475637858446479215407987 6713456787669718823111981)
    ·
      refine ⟨2517546295376144558666993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6713456787669718823111981 2517546295376144558666993)
      ·
        refine ⟨1888159721532108419000245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2517546295376144558666993 1888159721532108419000245)
        ·
          refine ⟨177014973893635164281273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1888159721532108419000245 177014973893635164281273)
          ·
            refine ⟨132761230420226373210955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177014973893635164281273 132761230420226373210955)
            ·
              refine ⟨199141845630339559816433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132761230420226373210955 199141845630339559816433)
              ·
                refine ⟨149356384222754669862325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199141845630339559816433 149356384222754669862325)
                ·
                  refine ⟨14002161020883250299593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149356384222754669862325 14002161020883250299593)
                  ·
                    rfl

theorem cell22_122711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 5].length) (baseStart_122711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122711 prefixEnd_122711 := by exact prefixLift 122711
  have htrace : WordTrace (prefixWord ++ tailWord_122711) baseStart_122711 baseEnd_122711 := by
    simpa [prefixWord, tailWord_122711, baseEnd_122711] using wordTrace_append hprefix tailTrace_122711
  have hstable : (prefixWord ++ tailWord_122711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122711).length < 2 ^ (prefixWord ++ tailWord_122711).sum := by decide
  have hdescent : baseEnd_122711 < baseStart_122711 := by decide
  rcases family_descends (prefixWord ++ tailWord_122711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122741 : List Nat := [1, 3, 4, 1, 1, 1, 4, 2, 1, 4]
def baseStart_122741 : Nat := 118140960795 + 122741 * 2 ^ 59
def prefixEnd_122741 : Nat := 4983230072969 + 3 ^ 40 * 122741 * 2
def baseEnd_122741 : Nat := 42016752675739672648687

theorem tailTrace_122741 : CollatzResearch.WordTrace tailWord_122741 prefixEnd_122741 42016752675739672648687 := by
  unfold tailWord_122741
  simp only [CollatzResearch.WordTrace]
  refine ⟨4476732048337794339000077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2984488032225196226000051 4476732048337794339000077)
  ·
    refine ⟨1678774518126672877125029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4476732048337794339000077 1678774518126672877125029)
    ·
      refine ⟨314770222148751164460943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1678774518126672877125029 314770222148751164460943)
      ·
        refine ⟨472155333223126746691415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314770222148751164460943 472155333223126746691415)
        ·
          refine ⟨708232999834690120037123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472155333223126746691415 708232999834690120037123)
          ·
            refine ⟨1062349499752035180055685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708232999834690120037123 1062349499752035180055685)
            ·
              refine ⟨199190531203506596260441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1062349499752035180055685 199190531203506596260441)
              ·
                refine ⟨149392898402629947195331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199190531203506596260441 149392898402629947195331)
                ·
                  refine ⟨224089347603944920792997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149392898402629947195331 224089347603944920792997)
                  ·
                    refine ⟨42016752675739672648687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 224089347603944920792997 42016752675739672648687)
                    ·
                      rfl

theorem cell22_122741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_122741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122741 prefixEnd_122741 := by exact prefixLift 122741
  have htrace : WordTrace (prefixWord ++ tailWord_122741) baseStart_122741 baseEnd_122741 := by
    simpa [prefixWord, tailWord_122741, baseEnd_122741] using wordTrace_append hprefix tailTrace_122741
  have hstable : (prefixWord ++ tailWord_122741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122741).length < 2 ^ (prefixWord ++ tailWord_122741).sum := by decide
  have hdescent : baseEnd_122741 < baseStart_122741 := by decide
  rcases family_descends (prefixWord ++ tailWord_122741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122752 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 1, 6]
def baseStart_122752 : Nat := 118140960795 + 122752 * 2 ^ 59
def prefixEnd_122752 : Nat := 4983230072969 + 3 ^ 40 * 122752 * 2
def baseEnd_122752 : Nat := 42020518200539310623653

theorem tailTrace_122752 : CollatzResearch.WordTrace tailWord_122752 prefixEnd_122752 42020518200539310623653 := by
  unfold tailWord_122752
  simp only [CollatzResearch.WordTrace]
  refine ⟨2238566625648971608825255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2984755500865295478433673 2238566625648971608825255)
  ·
    refine ⟨3357849938473457413237883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2238566625648971608825255 3357849938473457413237883)
    ·
      refine ⟨5036774907710186119856825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3357849938473457413237883 5036774907710186119856825)
      ·
        refine ⟨3777581180782639589892619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5036774907710186119856825 3777581180782639589892619)
        ·
          refine ⟨5666371771173959384838929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3777581180782639589892619 5666371771173959384838929)
          ·
            refine ⟨4249778828380469538629197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5666371771173959384838929 4249778828380469538629197)
            ·
              refine ⟨1593667060642676076985949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4249778828380469538629197 1593667060642676076985949)
              ·
                refine ⟨597625147741003528869731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1593667060642676076985949 597625147741003528869731)
                ·
                  refine ⟨896437721611505293304597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 597625147741003528869731 896437721611505293304597)
                  ·
                    refine ⟨42020518200539310623653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 896437721611505293304597 42020518200539310623653)
                    ·
                      rfl

theorem cell22_122752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_122752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122752 prefixEnd_122752 := by exact prefixLift 122752
  have htrace : WordTrace (prefixWord ++ tailWord_122752) baseStart_122752 baseEnd_122752 := by
    simpa [prefixWord, tailWord_122752, baseEnd_122752] using wordTrace_append hprefix tailTrace_122752
  have hstable : (prefixWord ++ tailWord_122752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122752).length < 2 ^ (prefixWord ++ tailWord_122752).sum := by decide
  have hdescent : baseEnd_122752 < baseStart_122752 := by decide
  rcases family_descends (prefixWord ++ tailWord_122752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122756 : List Nat := [2, 3, 2, 1, 1, 1, 5, 3, 4]
def baseStart_122756 : Nat := 118140960795 + 122756 * 2 ^ 59
def prefixEnd_122756 : Nat := 4983230072969 + 3 ^ 40 * 122756 * 2
def baseEnd_122756 : Nat := 14007295827428211174547

theorem tailTrace_122756 : CollatzResearch.WordTrace tailWord_122756 prefixEnd_122756 14007295827428211174547 := by
  unfold tailWord_122756
  simp only [CollatzResearch.WordTrace]
  refine ⟨2238639571641725950398061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2984852762188967933864081 2238639571641725950398061)
  ·
    refine ⟨839489839365647231399273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2238639571641725950398061 839489839365647231399273)
    ·
      refine ⟨629617379524235423549455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 839489839365647231399273 629617379524235423549455)
      ·
        refine ⟨944426069286353135324183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629617379524235423549455 944426069286353135324183)
        ·
          refine ⟨1416639103929529702986275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944426069286353135324183 1416639103929529702986275)
          ·
            refine ⟨2124958655894294554479413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416639103929529702986275 2124958655894294554479413)
            ·
              refine ⟨199214873990090114482445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2124958655894294554479413 199214873990090114482445)
              ·
                refine ⟨74705577746283792930917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199214873990090114482445 74705577746283792930917)
                ·
                  refine ⟨14007295827428211174547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74705577746283792930917 14007295827428211174547)
                  ·
                    rfl

theorem cell22_122756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_122756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122756 prefixEnd_122756 := by exact prefixLift 122756
  have htrace : WordTrace (prefixWord ++ tailWord_122756) baseStart_122756 baseEnd_122756 := by
    simpa [prefixWord, tailWord_122756, baseEnd_122756] using wordTrace_append hprefix tailTrace_122756
  have hstable : (prefixWord ++ tailWord_122756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122756).length < 2 ^ (prefixWord ++ tailWord_122756).sum := by decide
  have hdescent : baseEnd_122756 < baseStart_122756 := by decide
  rcases family_descends (prefixWord ++ tailWord_122756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122788 : List Nat := [2, 3, 1, 2, 1, 3, 4, 1, 2, 3]
def baseStart_122788 : Nat := 118140960795 + 122788 * 2 ^ 59
def prefixEnd_122788 : Nat := 4983230072969 + 3 ^ 40 * 122788 * 2
def baseEnd_122788 : Nat := 42032841736247216723543

theorem tailTrace_122788 : CollatzResearch.WordTrace tailWord_122788 prefixEnd_122788 42032841736247216723543 := by
  unfold tailWord_122788
  simp only [CollatzResearch.WordTrace]
  refine ⟨2239223139583760682980509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2985630852778347577307345 2239223139583760682980509)
  ·
    refine ⟨839708677343910256117691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2239223139583760682980509 839708677343910256117691)
    ·
      refine ⟨1259563016015865384176537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 839708677343910256117691 1259563016015865384176537)
      ·
        refine ⟨944672262011899038132403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1259563016015865384176537 944672262011899038132403)
        ·
          refine ⟨1417008393017848557198605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944672262011899038132403 1417008393017848557198605)
          ·
            refine ⟨531378147381693208949477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1417008393017848557198605 531378147381693208949477)
            ·
              refine ⟨99633402634067476678027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 531378147381693208949477 99633402634067476678027)
              ·
                refine ⟨149450103951101215017041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99633402634067476678027 149450103951101215017041)
                ·
                  refine ⟨112087577963325911262781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149450103951101215017041 112087577963325911262781)
                  ·
                    refine ⟨42032841736247216723543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112087577963325911262781 42032841736247216723543)
                    ·
                      rfl

theorem cell22_122788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_122788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122788 prefixEnd_122788 := by exact prefixLift 122788
  have htrace : WordTrace (prefixWord ++ tailWord_122788) baseStart_122788 baseEnd_122788 := by
    simpa [prefixWord, tailWord_122788, baseEnd_122788] using wordTrace_append hprefix tailTrace_122788
  have hstable : (prefixWord ++ tailWord_122788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122788).length < 2 ^ (prefixWord ++ tailWord_122788).sum := by decide
  have hdescent : baseEnd_122788 < baseStart_122788 := by decide
  rcases family_descends (prefixWord ++ tailWord_122788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122792 : List Nat := [2, 1, 6, 2, 2, 1, 1, 2, 1, 4]
def baseStart_122792 : Nat := 118140960795 + 122792 * 2 ^ 59
def prefixEnd_122792 : Nat := 4983230072969 + 3 ^ 40 * 122792 * 2
def baseEnd_122792 : Nat := 42034211017992539623531

theorem tailTrace_122792 : CollatzResearch.WordTrace tailWord_122792 prefixEnd_122792 42034211017992539623531 := by
  unfold tailWord_122792
  simp only [CollatzResearch.WordTrace]
  refine ⟨2239296085576515024553315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2985728114102020032737753 2239296085576515024553315)
  ·
    refine ⟨3358944128364772536829973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2239296085576515024553315 3358944128364772536829973)
    ·
      refine ⟨157450506017098712663905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3358944128364772536829973 157450506017098712663905)
      ·
        refine ⟨118087879512824034497929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157450506017098712663905 118087879512824034497929)
        ·
          refine ⟨88565909634618025873447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118087879512824034497929 88565909634618025873447)
          ·
            refine ⟨132848864451927038810171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88565909634618025873447 132848864451927038810171)
            ·
              refine ⟨199273296677890558215257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132848864451927038810171 199273296677890558215257)
              ·
                refine ⟨149454972508417918661443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199273296677890558215257 149454972508417918661443)
                ·
                  refine ⟨224182458762626877992165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149454972508417918661443 224182458762626877992165)
                  ·
                    refine ⟨42034211017992539623531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 224182458762626877992165 42034211017992539623531)
                    ·
                      rfl

theorem cell22_122792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_122792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122792 prefixEnd_122792 := by exact prefixLift 122792
  have htrace : WordTrace (prefixWord ++ tailWord_122792) baseStart_122792 baseEnd_122792 := by
    simpa [prefixWord, tailWord_122792, baseEnd_122792] using wordTrace_append hprefix tailTrace_122792
  have hstable : (prefixWord ++ tailWord_122792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122792).length < 2 ^ (prefixWord ++ tailWord_122792).sum := by decide
  have hdescent : baseEnd_122792 < baseStart_122792 := by decide
  rcases family_descends (prefixWord ++ tailWord_122792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122799 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 5, 3]
def baseStart_122799 : Nat := 118140960795 + 122799 * 2 ^ 59
def prefixEnd_122799 : Nat := 4983230072969 + 3 ^ 40 * 122799 * 2
def baseEnd_122799 : Nat := 42036607261046854698509

theorem tailTrace_122799 : CollatzResearch.WordTrace tailWord_122799 prefixEnd_122799 42036607261046854698509 := by
  unfold tailWord_122799
  simp only [CollatzResearch.WordTrace]
  refine ⟨4478847482127670244611451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2985898321418446829740967 4478847482127670244611451)
  ·
    refine ⟨6718271223191505366917177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4478847482127670244611451 6718271223191505366917177)
    ·
      refine ⟨5038703417393629025187883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6718271223191505366917177 5038703417393629025187883)
      ·
        refine ⟨7558055126090443537781825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5038703417393629025187883 7558055126090443537781825)
        ·
          refine ⟨5668541344567832653336369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7558055126090443537781825 5668541344567832653336369)
          ·
            refine ⟨4251406008425874490002277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5668541344567832653336369 4251406008425874490002277)
            ·
              refine ⟨797138626579851466875427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4251406008425874490002277 797138626579851466875427)
              ·
                refine ⟨1195707939869777200313141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797138626579851466875427 1195707939869777200313141)
                ·
                  refine ⟨112097619362791612529357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1195707939869777200313141 112097619362791612529357)
                  ·
                    refine ⟨42036607261046854698509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112097619362791612529357 42036607261046854698509)
                    ·
                      rfl

theorem cell22_122799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 3].length) (baseStart_122799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122799 prefixEnd_122799 := by exact prefixLift 122799
  have htrace : WordTrace (prefixWord ++ tailWord_122799) baseStart_122799 baseEnd_122799 := by
    simpa [prefixWord, tailWord_122799, baseEnd_122799] using wordTrace_append hprefix tailTrace_122799
  have hstable : (prefixWord ++ tailWord_122799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122799).length < 2 ^ (prefixWord ++ tailWord_122799).sum := by decide
  have hdescent : baseEnd_122799 < baseStart_122799 := by decide
  rcases family_descends (prefixWord ++ tailWord_122799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122850 : List Nat := [3, 3, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_122850 : Nat := 118140960795 + 122850 * 2 ^ 59
def prefixEnd_122850 : Nat := 4983230072969 + 3 ^ 40 * 122850 * 2
def baseEnd_122850 : Nat := 42054065603299721673353

theorem tailTrace_122850 : CollatzResearch.WordTrace tailWord_122850 prefixEnd_122850 42054065603299721673353 := by
  unfold tailWord_122850
  simp only [CollatzResearch.WordTrace]
  refine ⟨1120176901235726488679501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2987138403295270636478669 1120176901235726488679501)
  ·
    refine ⟨420066337963397433254813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1120176901235726488679501 420066337963397433254813)
    ·
      refine ⟨157524876736274037470555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420066337963397433254813 157524876736274037470555)
      ·
        refine ⟨236287315104411056205833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157524876736274037470555 236287315104411056205833)
        ·
          refine ⟨177215486328308292154375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236287315104411056205833 177215486328308292154375)
          ·
            refine ⟨265823229492462438231563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177215486328308292154375 265823229492462438231563)
            ·
              refine ⟨398734844238693657347345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265823229492462438231563 398734844238693657347345)
              ·
                refine ⟨299051133179020243010509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398734844238693657347345 299051133179020243010509)
                ·
                  refine ⟨112144174942132591128941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299051133179020243010509 112144174942132591128941)
                  ·
                    refine ⟨42054065603299721673353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112144174942132591128941 42054065603299721673353)
                    ·
                      rfl

theorem cell22_122850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_122850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122850 prefixEnd_122850 := by exact prefixLift 122850
  have htrace : WordTrace (prefixWord ++ tailWord_122850) baseStart_122850 baseEnd_122850 := by
    simpa [prefixWord, tailWord_122850, baseEnd_122850] using wordTrace_append hprefix tailTrace_122850
  have hstable : (prefixWord ++ tailWord_122850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122850).length < 2 ^ (prefixWord ++ tailWord_122850).sum := by decide
  have hdescent : baseEnd_122850 < baseStart_122850 := by decide
  rcases family_descends (prefixWord ++ tailWord_122850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122876 : List Nat := [2, 2, 2, 1, 2, 2, 3, 3, 1, 4]
def baseStart_122876 : Nat := 118140960795 + 122876 * 2 ^ 59
def prefixEnd_122876 : Nat := 4983230072969 + 3 ^ 40 * 122876 * 2
def baseEnd_122876 : Nat := 42062965934644320523273

theorem tailTrace_122876 : CollatzResearch.WordTrace tailWord_122876 prefixEnd_122876 42062965934644320523273 := by
  unfold tailWord_122876
  simp only [CollatzResearch.WordTrace]
  refine ⟨2240827951424356197582241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2987770601899141596776321 2240827951424356197582241)
  ·
    refine ⟨1680620963568267148186681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2240827951424356197582241 1680620963568267148186681)
    ·
      refine ⟨1260465722676200361140011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1680620963568267148186681 1260465722676200361140011)
      ·
        refine ⟨1890698584014300541710017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1260465722676200361140011 1890698584014300541710017)
        ·
          refine ⟨1418023938010725406282513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1890698584014300541710017 1418023938010725406282513)
          ·
            refine ⟨1063517953508044054711885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1418023938010725406282513 1063517953508044054711885)
            ·
              refine ⟨398819232565516520516957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1063517953508044054711885 398819232565516520516957)
              ·
                refine ⟨149557212212068695193859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398819232565516520516957 149557212212068695193859)
                ·
                  refine ⟨224335818318103042790789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149557212212068695193859 224335818318103042790789)
                  ·
                    refine ⟨42062965934644320523273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 224335818318103042790789 42062965934644320523273)
                    ·
                      rfl

theorem cell22_122876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_122876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122876 prefixEnd_122876 := by exact prefixLift 122876
  have htrace : WordTrace (prefixWord ++ tailWord_122876) baseStart_122876 baseEnd_122876 := by
    simpa [prefixWord, tailWord_122876, baseEnd_122876] using wordTrace_append hprefix tailTrace_122876
  have hstable : (prefixWord ++ tailWord_122876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122876).length < 2 ^ (prefixWord ++ tailWord_122876).sum := by decide
  have hdescent : baseEnd_122876 < baseStart_122876 := by decide
  rcases family_descends (prefixWord ++ tailWord_122876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122891 : List Nat := [1, 1, 1, 1, 6, 1, 1, 6, 4]
def baseStart_122891 : Nat := 118140960795 + 122891 * 2 ^ 59
def prefixEnd_122891 : Nat := 4983230072969 + 3 ^ 40 * 122891 * 2
def baseEnd_122891 : Nat := 14022700247063093799409

theorem tailTrace_122891 : CollatzResearch.WordTrace tailWord_122891 prefixEnd_122891 14022700247063093799409 := by
  unfold tailWord_122891
  simp only [CollatzResearch.WordTrace]
  refine ⟨4482202997794369956960527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2988135331862913304640351 4482202997794369956960527)
  ·
    refine ⟨6723304496691554935440791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4482202997794369956960527 6723304496691554935440791)
    ·
      refine ⟨10084956745037332403161187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6723304496691554935440791 10084956745037332403161187)
      ·
        refine ⟨15127435117555998604741781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10084956745037332403161187 15127435117555998604741781)
        ·
          refine ⟨709098521135437434597271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15127435117555998604741781 709098521135437434597271)
          ·
            refine ⟨1063647781703156151895907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709098521135437434597271 1063647781703156151895907)
            ·
              refine ⟨1595471672554734227843861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063647781703156151895907 1595471672554734227843861)
              ·
                refine ⟨74787734651003166930181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1595471672554734227843861 74787734651003166930181)
                ·
                  refine ⟨14022700247063093799409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74787734651003166930181 14022700247063093799409)
                  ·
                    rfl

theorem cell22_122891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 4].length) (baseStart_122891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122891 prefixEnd_122891 := by exact prefixLift 122891
  have htrace : WordTrace (prefixWord ++ tailWord_122891) baseStart_122891 baseEnd_122891 := by
    simpa [prefixWord, tailWord_122891, baseEnd_122891] using wordTrace_append hprefix tailTrace_122891
  have hstable : (prefixWord ++ tailWord_122891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122891).length < 2 ^ (prefixWord ++ tailWord_122891).sum := by decide
  have hdescent : baseEnd_122891 < baseStart_122891 := by decide
  rcases family_descends (prefixWord ++ tailWord_122891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122904 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 3, 6]
def baseStart_122904 : Nat := 118140960795 + 122904 * 2 ^ 59
def prefixEnd_122904 : Nat := 4983230072969 + 3 ^ 40 * 122904 * 2
def baseEnd_122904 : Nat := 42072550906861580823187

theorem tailTrace_122904 : CollatzResearch.WordTrace tailWord_122904 prefixEnd_122904 42072550906861580823187 := by
  unfold tailWord_122904
  simp only [CollatzResearch.WordTrace]
  refine ⟨2241338573373636588591883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2988451431164848784789177 2241338573373636588591883)
  ·
    refine ⟨3362007860060454882887825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2241338573373636588591883 3362007860060454882887825)
    ·
      refine ⟨2521505895045341162165869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3362007860060454882887825 2521505895045341162165869)
      ·
        refine ⟨945564710642002935812201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2521505895045341162165869 945564710642002935812201)
        ·
          refine ⟨709173532981502201859151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 945564710642002935812201 709173532981502201859151)
          ·
            refine ⟨1063760299472253302788727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709173532981502201859151 1063760299472253302788727)
            ·
              refine ⟨1595640449208379954183091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063760299472253302788727 1595640449208379954183091)
              ·
                refine ⟨2393460673812569931274637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595640449208379954183091 2393460673812569931274637)
                ·
                  refine ⟨897547752679713724227989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2393460673812569931274637 897547752679713724227989)
                  ·
                    refine ⟨42072550906861580823187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 897547752679713724227989 42072550906861580823187)
                    ·
                      rfl

theorem cell22_122904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_122904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122904 prefixEnd_122904 := by exact prefixLift 122904
  have htrace : WordTrace (prefixWord ++ tailWord_122904) baseStart_122904 baseEnd_122904 := by
    simpa [prefixWord, tailWord_122904, baseEnd_122904] using wordTrace_append hprefix tailTrace_122904
  have hstable : (prefixWord ++ tailWord_122904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122904).length < 2 ^ (prefixWord ++ tailWord_122904).sum := by decide
  have hdescent : baseEnd_122904 < baseStart_122904 := by decide
  rcases family_descends (prefixWord ++ tailWord_122904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
